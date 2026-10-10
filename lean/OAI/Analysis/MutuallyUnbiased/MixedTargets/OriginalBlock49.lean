import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock49 : Integer.Sparse (Fin 2886) := [(1568, -3096668160), (1569, -24524249760), (1570, -27254740800), (1571, -32184268800), (1572, -14870793600), (1573, -12493459200), (1574, -20960256960), (1575, -27915675840), (1576, 9764081280), (1577, -6390299520), (1578, 12237903360), (1579, -966442560), (1580, -21563601600), (1581, -40147420800), (1582, 144824639040), (1583, 49328320320), (1584, -67755787200), (1585, -20345959680), (1586, -29600006400), (1587, -28211256000), (1588, -2243173600), (1589, 59941831200), (1590, 15821971360), (1591, 90244812800), (1592, 79604035200), (1593, 11104874400), (1594, 3560809200), (1595, 2243173600), (1596, 18261313760), (1597, -121446125600), (1598, -83050905600), (1599, -11104874400)]

def originalBlock49 : Integer.Sparse OriginalKey := [(Sum.inl 610, -104801284800), (Sum.inl 613, -122621248800), (Sum.inl 618, -15483340800), (Sum.inl 929, 61189516800), (Sum.inl 932, 48820406400), (Sum.inl 937, -74353968000), (Sum.inl 1044, -139578379200), (Sum.inl 1049, -160921344000), (Sum.inl 1087, -136273704000), (Sum.inl 1818, -62467296000), (Sum.inl 2338, -4832212800), (Sum.inl 2341, -31951497600), (Sum.inl 2769, -148000032000), (Sum.inl 2789, -107818008000), (Sum.inl 2865, -415254528000), (Sum.inl 2878, 55524372000), (Sum.inl 2882, -55524372000), (Sum.inl 2885, 79109856800), (Sum.inl 2886, 91306568800), (Sum.inl 2888, 246641601600), (Sum.inl 2928, 398020176000), (Sum.inl 2930, -101729798400), (Sum.inl 2951, 451224064000), (Sum.inl 2952, -338778936000), (Sum.inl 2955, -607230628000), (Sum.inl 2964, -141056280000), (Sum.inl 2967, -200737104000), (Sum.inl 3051, -11215868000), (Sum.inl 3055, 11215868000), (Sum.inl 3074, 17804046000), (Sum.inl 3097, 299709156000), (Sum.inl 3098, 724123195200)]

theorem originalBlockCheck49 : originalBlock49 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock49 keyMomentRows) := by decide +kernel

theorem originalBlockEval49 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock49 x =
      Integer.Sparse.eval keyPolynomialBlock49 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck49, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
