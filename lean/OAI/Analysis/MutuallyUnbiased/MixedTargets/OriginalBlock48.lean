import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock48 : Integer.Sparse (Fin 2886) := [(1536, -840140160), (1537, -63071485440), (1538, 7230439680), (1539, 12493459200), (1540, -24973506720), (1541, -22104192000), (1542, -8201856960), (1543, -60036387840), (1544, 22800864960), (1545, -18961989120), (1546, -21544810560), (1547, 1362458880), (1548, 13514102400), (1549, -25670966400), (1550, 47794132800), (1551, -2266787520), (1552, -2484794880), (1553, -41107896000), (1554, -45977080320), (1555, 2266787520), (1556, 54185688000), (1557, -2970057600), (1558, -24973506720), (1559, 22104192000), (1560, -60504474240), (1561, 98417945280), (1562, -2661295680), (1563, 18961989120), (1564, 2970057600), (1565, 62675469120), (1566, 57263882880), (1567, -13077792000)]

def originalBlock48 : Integer.Sparse OriginalKey := [(Sum.inl 1138, -302522371200), (Sum.inl 1143, -124867533600), (Sum.inl 1802, 62467296000), (Sum.inl 1805, -14850288000), (Sum.inl 1807, 94809945600), (Sum.inl 1810, -94809945600), (Sum.inl 1811, -12423974400), (Sum.inl 1812, -229885401600), (Sum.inl 1815, 14850288000), (Sum.inl 1819, -124867533600), (Sum.inl 2431, 286319414400), (Sum.inl 2483, 313377345600), (Sum.inl 2488, -13306478400), (Sum.inl 2515, 492089726400), (Sum.inl 2522, 110520960000), (Sum.inl 2814, -107724052800), (Sum.inl 2817, -41009284800), (Sum.inl 2896, 11333937600), (Sum.inl 3397, -110520960000), (Sum.inl 3619, -128354832000), (Sum.inl 3671, 67570512000), (Sum.inl 3692, 6812294400), (Sum.inl 3693, 114004324800), (Sum.inl 3706, -300181939200), (Sum.inl 3709, -65388960000), (Sum.inl 3719, 36152198400), (Sum.inl 3721, 270928440000), (Sum.inl 3731, -11333937600), (Sum.inl 3782, -4200700800), (Sum.inl 3801, -315357427200), (Sum.inl 3899, 238970664000), (Sum.inl 4025, -205539480000)]

theorem originalBlockCheck48 : originalBlock48 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock48 keyMomentRows) := by decide +kernel

theorem originalBlockEval48 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock48 x =
      Integer.Sparse.eval keyPolynomialBlock48 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck48, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
