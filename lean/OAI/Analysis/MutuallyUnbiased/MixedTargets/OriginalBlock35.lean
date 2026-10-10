import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock35 : Integer.Sparse (Fin 2886) := [(1120, -9410139840), (1121, -22619797440), (1122, -37160467200), (1123, -41039222400), (1124, -9714124800), (1125, 8983886400), (1126, -44251121280), (1127, 32398181760), (1128, 37160467200), (1129, 41036906880), (1130, -3043320000), (1131, 20813687520), (1132, -6731640000), (1133, -32827296960), (1134, 21079798560), (1135, -3096668160), (1136, -32100528000), (1137, 28835668800), (1138, -24524249760), (1139, 13071264960), (1140, -33681320640), (1141, 2919001920), (1142, -20960256960), (1143, 27444600000), (1144, 16110261120), (1145, 6236720640), (1146, 31687339200), (1147, 122837110080), (1148, -9576076800), (1149, -130091384000), (1150, 18828969360), (1151, -2489739840)]

def originalBlock35 : Integer.Sparse OriginalKey := [(Sum.inl 2294, -15483340800), (Sum.inl 2742, 614185550400), (Sum.inl 2744, 104068437600), (Sum.inl 2783, -48570624000), (Sum.inl 2789, -15216600000), (Sum.inl 3054, -47880384000), (Sum.inl 3098, 44919432000), (Sum.inl 3525, -185802336000), (Sum.inl 3526, -205196112000), (Sum.inl 3535, -47050699200), (Sum.inl 3541, -113098987200), (Sum.inl 3572, 185802336000), (Sum.inl 3573, 205184534400), (Sum.inl 3583, -221255606400), (Sum.inl 3584, 161990908800), (Sum.inl 3618, 31183603200), (Sum.inl 3619, -104801284800), (Sum.inl 3622, 137223000000), (Sum.inl 3623, 144178344000), (Sum.inl 3625, 80551305600), (Sum.inl 3626, -135069948000), (Sum.inl 3627, 65356324800), (Sum.inl 3628, -168406603200), (Sum.inl 3629, -164136484800), (Sum.inl 3632, 14595009600), (Sum.inl 3633, 105398992800), (Sum.inl 3635, -160502640000), (Sum.inl 3636, -33658200000), (Sum.inl 3817, 94144846800), (Sum.inl 4084, 158436696000), (Sum.inl 4092, -650456920000)]

theorem originalBlockCheck35 : originalBlock35 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock35 keyMomentRows) := by decide +kernel

theorem originalBlockEval35 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock35 x =
      Integer.Sparse.eval keyPolynomialBlock35 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck35, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
