import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock2 : Integer.Sparse (Fin 2886) := [(64, -2834735040), (65, 717984160), (66, -21141114240), (67, -6613813440), (68, -21991292160), (69, 522207360), (70, -8913645120), (71, 13312972800), (72, 8842310400), (73, -1957576320), (74, 1333725120), (75, 3083921280), (76, -10640588880), (77, -14963621760), (78, -3626979840), (79, 23045362560), (80, -7955241120), (81, 21563723520), (82, 2928539040), (83, -545198400), (84, 34097686560), (85, 19375987680), (86, -23647759680), (87, -12379132800), (88, -11714846400), (89, -11204730240), (90, 1379616000), (91, 11172102240), (92, -1541328000), (93, 15006748800), (94, 9445352256), (95, 33069067200)]

def originalBlock2 : Integer.Sparse OriginalKey := [(Sum.inl 148, -105705571200), (Sum.inl 159, -14173675200), (Sum.inl 165, 47226761280), (Sum.inl 166, -174262449600), (Sum.inl 170, 14642695200), (Sum.inl 181, 107818617600), (Sum.inl 188, -18134899200), (Sum.inl 191, 165345336000), (Sum.inl 193, 75033744000), (Sum.inl 194, -2725992000), (Sum.inl 208, -61895664000), (Sum.inl 218, -58574232000), (Sum.inl 225, 130712227200), (Sum.inl 228, 115226812800), (Sum.inl 246, -7706640000), (Sum.inl 250, -74818108800), (Sum.inl 258, 96879938400), (Sum.inl 263, 55860511200), (Sum.inl 264, -46304864400), (Sum.inl 271, 15419606400), (Sum.inl 328, -9787881600), (Sum.inl 340, 66564864000), (Sum.inl 342, -33069067200), (Sum.inl 367, 6668625600), (Sum.inl 387, 44211552000), (Sum.inl 388, 3589920800), (Sum.inl 406, -109956460800), (Sum.inl 413, 2611036800), (Sum.inl 416, -44568225600)]

theorem originalBlockCheck2 : originalBlock2 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock2 keyMomentRows) := by decide +kernel

theorem originalBlockEval2 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock2 x =
      Integer.Sparse.eval keyPolynomialBlock2 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck2, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
