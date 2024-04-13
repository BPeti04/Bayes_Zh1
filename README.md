# Bayes_ZH1
1.1
```
var feature1 = ['könyvtáros','tanár'];
var feature2 = ['csendes','cserfes'];
var operator = [' és ',' vagy '];

var ComplexModel1 = function() {
    var word1 = uniformDraw(feature1);
    var op = uniformDraw(operator);
    var word2 = uniformDraw(feature2);
    var word3 = uniformDraw(feature2);
    
    // Diszlexiás ágens esetén véletlenszerűen felcseréljük a 'csendes' és 'cserfes' szavakat
    var diszlexias = Random.boolean();
    if (diszlexias) {
        var temp = word2;
        word2 = word3;
        word3 = temp;
    }
  
    print('Premissza: Panni ' + word1 + op + word2 + '.'); 
    print('Konklúzió: Panni ' + word3 + '.'); 
    
    var ervenyes = (op === ' és ')
                   ? ((word2 === word3) ? 'érvényes' : 'nem érvényes') 
                   : 'nem érvényes';
    print(ervenyes); 
    return ervenyes;
}

var output = Infer({model: ComplexModel1, method:'rejection', samples: 1});
```

1.2
```
var feature1 = ['könyvtáros','tanár'];
var feature2 = ['csendes','cserfes'];
var operator = [' és ',' vagy '];

var ComplexModel2 = function() {
    var word1 = uniformDraw(feature1);
    
    // A logikai operátor ("és" vagy "vagy") kiválasztása
    var op = uniformDraw(operator);
    var klasszikusEs = flip(0.95); // 95%-os valószínűség klasszikus "és"-re
    if (!klasszikusEs) {
        op = ' vagy '; // 80%-os valószínűség "vagy"-ra, ha nem klasszikus "és"
    }
    
    var word2 = uniformDraw(feature2);
  
    // Ha "és" operátor van, akkor a második tulajdonságnak meg kell egyeznie a következtetésben
    // Ha "vagy" operátor van, akkor a következtetésben a két tulajdonság közül egyiknek sem kell megfelelnie
    var word3 = (op === ' és ') ? word2 : uniformDraw(feature2.filter(function(item) { return item !== word2; }));
    
    print('Premissza: Panni ' + word1 + op + word2 + '.'); 
    print('Konklúzió: Panni ' + word1 + '.'); 
    
    var ervenyes = (op === ' és ')
                   ? ((word2 === word3) ? 'érvényes' : 'nem érvényes') 
                   : 'érvényes'; // "vagy" esetén mindig érvényes az inferencia
    print(ervenyes); 
    return ervenyes;
}

var output = Infer({model: ComplexModel2, method:'rejection', samples: 1});

```
1.3
```
var P_legalabb_4 = 1 - (1 / 6) * (1 / 6);
print("Az összeg legalább 4 lesz valószínűsége: " + P_legalabb_4);
```
1.4
```
var KingAceParadox = function() {
    var vanAsz = flip(0.5); // 50% eséllyel van ász a kezedben
    var vanKiraly = flip(0.5); // 50% eséllyel van király a kezedben
    
    var vagyTipus = uniformDraw(["és", "vagy", "kizáró vagy"]); // Választás az értelmezés típusa között
    
    var konkluzio;
    if (vagyTipus === "és") {
        konkluzio = vanAsz && vanKiraly; // Mindkét feltételnek egyszerre igaznak kell lennie
    } else if (vagyTipus === "vagy") {
        konkluzio = vanAsz || vanKiraly; // Legalább az egyik feltételnek igaznak kell lennie
    } else {
        konkluzio = vanAsz !== vanKiraly; // Mindkét feltétel nem lehet egyszerre igaz
    }
    
    return konkluzio;
}

var output = Infer({model: KingAceParadox, method:'rejection', samples: 1000});
viz.auto(output);
```

2.1
```
Lemma problem_1 : forall A B C : Prop, A /\ (B\/C) -> (A/\B) \/ (A/\C).
Proof.
intros.
intuition.

Lemma problem_1 : forall A B C : Prop, A /\ (B\/C) -> (A/\B) \/ (A/\C).
Proof.
intros.
destruct H as [H1 H2].
elim H2.
intros.
left.
split.
auto.
auto.
```
2.2

```
Lemma problem_2: forall A B C: Prop, ((B -> A) /\ (C -> A)) ->((B\/C ->A)).
Proof.
firstorder.
```
2.3
```
Lemma problem_3 : forall A B: Prop, (A\/~A) -> ((A->B)->A) -> A.
Proof.
intros.
elim H.
intros.
auto.
```
2.4 - 

3.1
```
var model = function() {
    // Királyok és nem királyok száma a francia kártyapakliban
    var kiralyok_szama = 4;
    var nem_kiralyok_szama = 52 - kiralyok_szama;
    
    // Első kártya kiválasztása
    var elso_kartya_szin = randomInteger(4) + 1; // Véletlenszerűen választunk egy színt
    var elso_kartya_figura = randomInteger(13) + 1; // Véletlenszerűen választunk egy figurát
    
    // Második kártya kiválasztása
    var masodik_kartya_szin = randomInteger(4) + 1; // Véletlenszerűen választunk egy színt
    var masodik_kartya_figura = randomInteger(13) + 1; // Véletlenszerűen választunk egy figurát
    
    // Ellenőrizzük, hogy az egyik kártya király-e, a másik pedig nem király
    var egyik_kiraly_masik_nem_kiraly = 
        ((elso_kartya_figura === 13 && elso_kartya_szin !== 1) || (masodik_kartya_figura === 13 && masodik_kartya_szin !== 1)) ||
        ((elso_kartya_figura !== 13 && elso_kartya_szin === 1) || (masodik_kartya_figura !== 13 && masodik_kartya_szin === 1));
    
    // Visszaadjuk az eredményt
    return { 'egyik_kiraly_masik_nem_kiraly': egyik_kiraly_masik_nem_kiraly };
};

// Enumerate() segítségével kiszámoljuk az eloszlást a model szerint
var eloszlas = Enumerate(model);

// Kiírjuk az eloszlást
print(eloszlas);
```
3.2
```
var model = function() {
    var X = randomInteger(4); // X egyenletesen eloszlik {0, 1, 2, 3} között
    var Y = randomInteger(4); // Y egyenletesen eloszlik {0, 1, 2, 3} között
    var Z = randomInteger(4); // Z egyenletesen eloszlik {0, 1, 2, 3} között
    
    var W = X + Y + Z; // W értéke X, Y és Z összege
    
    // Ha W értéke 7
    condition(W === 7);
    
    // Visszaadjuk az X értékét
    return X;
};

// Enumerate() segítségével kiszámoljuk az X eloszlását, feltéve, hogy W = 7
var eloszlas = Enumerate(model);

// Kiírjuk az eloszlást
print(eloszlas);
```

3.3 
```
// Monty Hall probléma szimulációja
var montyHall = function() {
    // Három ajtó közül véletlenszerűen választunk egyet, ahol az autó lehet
    var helyes_ajto = randomInteger(3) + 1;
    
    // A játékos választ egy ajtót
    var jatekos_valasztas = randomInteger(3) + 1;
    
    // A házigazda választ egy ajtót, hogy mutasson egy kecskét
    var hazigazda_valasztas;
    do {
        hazigazda_valasztas = randomInteger(3) + 1;
    } while (hazigazda_valasztas === helyes_ajto || hazigazda_valasztas === jatekos_valasztas);
    
    // A játékos választhat, hogy marad a választásában, vagy vált egy másik ajtóra
    var marad = jatekos_valasztas === helyes_ajto;
    
    // Visszaadjuk az eredményt, és hogy a játékos nyert-e
    return { marad: marad, nyert: marad ? 1 : 0 };
};

// Több mintavétel a Monty Hall játékból
var mintavetel = Infer({ method: 'enumerate' }, montyHall);

// Kiírjuk az eredményeket
viz.auto(mintavetel);
```

3.4
```
var montyHallWithHelper = function () {
    var car = categorical({ps:[1/3,1/3,1/3], vs:[1, 2, 3]});
    var initialChoice = categorical({ps:[1/3,1/3,1/3], vs:[1, 2, 3]});
    var montyOptions = (car === initialChoice) ? [1, 2, 3].filter(x => x !== initialChoice) : [1, 2, 3].filter(x => x !== car && x !== initialChoice);
    
    // Beépített ember, aki 50% valószínűséggel helyesen mutatja meg egy kecskét
    var montyChoice = flip(0.5) ? categorical({ps:[1/2, 1/2], vs: montyOptions}) : montyOptions.filter(x => x !== car)[0];
    
    // Monty által ajánlott ajtó
    var suggestedDoor = (initialChoice === montyChoice) ? car : montyOptions.filter(x => x !== montyChoice && x !== initialChoice)[0];
    
    // Nyertünk-e a maradás stratégiával?
    var stayStrategyOutcome = (initialChoice === car) ? 'nyer' : 'veszít';
    
    // Nyertünk-e a váltás stratégiával?
    var switchStrategyOutcome = (suggestedDoor === car) ? 'nyer' : 'veszít';
    
    return {
        stayStrategyOutcome: stayStrategyOutcome,
        switchStrategyOutcome: switchStrategyOutcome
    };
};

var distribution = Enumerate(montyHallWithHelper);

viz.marginals(distribution);
```
