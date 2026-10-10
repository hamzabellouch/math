import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock90 : Integer.Sparse (Fin 2886) := [(2880, 7075401600), (2881, 8422128000), (2882, -10373020800), (2883, -1439851200), (2884, 1439851200), (2885, 15559531200)]

def originalBlock90 : Integer.Sparse OriginalKey := [(Sum.inl 1505, 8422128000), (Sum.inl 1515, 15559531200), (Sum.inl 2148, -10373020800), (Sum.inl 3255, 7075401600), (Sum.inl 3261, 1439851200), (Sum.inl 3511, -1439851200), (Sum.inl 4151, 33688512000), (Sum.inl 4155, 62238124800), (Sum.inl 4527, 28301606400), (Sum.inl 4530, 5759404800), (Sum.inl 4666, -41492083200), (Sum.inl 4958, -5759404800)]

theorem originalBlockCheck90 : originalBlock90 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock90 keyMomentRows) := by decide +kernel

theorem originalBlockEval90 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock90 x =
      Integer.Sparse.eval keyPolynomialBlock90 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck90, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
