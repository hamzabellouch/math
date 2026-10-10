import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock14 : Integer.Sparse (Fin 2886) := [(448, -6166598400), (449, 27472187520), (450, -6062232000), (451, -2366887680), (452, -7602509760), (453, 6166598400), (454, -11702125440), (455, -59335206720), (456, -5277668160), (457, -35596375200), (458, 20905332480), (459, -10054512000), (460, -2973138240), (461, -1455396480), (462, 4922282880), (463, -778565760), (464, 3114263040), (465, -4922282880), (466, -21031476480), (467, 1455396480), (468, -606706560), (469, -4671394560), (470, 6062232000), (471, 21031476480), (472, -11702125440), (473, 2973138240), (474, -658082400), (475, 1213413120), (476, 10054512000), (477, 8919414720), (478, -11017584640), (479, -3178736640)]

def originalBlock14 : Integer.Sparse OriginalKey := [(Sum.inl 38, -15893683200), (Sum.inl 127, -58510627200), (Sum.inl 160, -55087923200), (Sum.inl 175, 50272560000), (Sum.inl 178, -50272560000), (Sum.inl 179, 24611414400), (Sum.inl 180, -24611414400), (Sum.inl 286, -58510627200), (Sum.inl 295, 44597073600), (Sum.inl 306, -3290412000), (Sum.inl 314, 14865691200), (Sum.inl 316, 30311160000), (Sum.inl 317, 7276982400), (Sum.inl 335, 105157382400), (Sum.inl 343, -23356972800), (Sum.inl 369, -30311160000), (Sum.inl 424, -14865691200), (Sum.inl 432, -177981876000), (Sum.inl 438, -296676033600), (Sum.inl 448, -3033532800), (Sum.inl 449, 150930969600), (Sum.inl 450, 6067065600), (Sum.inl 451, 137360937600), (Sum.inl 471, -105157382400), (Sum.inl 490, -26388340800), (Sum.inl 492, -7276982400), (Sum.inl 496, -42667430400), (Sum.inl 505, -41905377600)]

theorem originalBlockCheck14 : originalBlock14 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock14 keyMomentRows) := by decide +kernel

theorem originalBlockEval14 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock14 x =
      Integer.Sparse.eval keyPolynomialBlock14 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck14, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
