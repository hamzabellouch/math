import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock15 : Integer.Sparse (Fin 2886) := [(480, 2366887680), (481, -14184489600), (482, 3912211200), (483, 28348864640), (484, 2943398400), (485, -20905332480), (486, -606706560), (487, 2969668800), (488, -8378760000), (489, 6052872960), (490, -10555336320), (491, 12705079680), (492, -8919414720), (493, -9079309440), (494, -4339159680), (495, -4783584000), (496, 6003054720), (497, -880757400), (498, 21394965600), (499, -4891350000), (500, -2449600320), (501, 1823596800), (502, -4842156000), (503, -21394965600), (504, 4891350000), (505, 3368200440), (506, 4088628400), (507, -11693349600), (508, 4891350000), (509, 3368200440), (510, 4752056000), (511, 14137403000)]

def originalBlock15 : Integer.Sparse OriginalKey := [(Sum.inl 33, -70922448000), (Sum.inl 65, -45396547200), (Sum.inl 68, 63525398400), (Sum.inl 71, 14848344000), (Sum.inl 95, 30264364800), (Sum.inl 98, 14716992000), (Sum.inl 111, 19561056000), (Sum.inl 186, -41893800000), (Sum.inl 275, -44597073600), (Sum.inl 328, 30015273600), (Sum.inl 339, -52776681600), (Sum.inl 343, -104526662400), (Sum.inl 345, 24456750000), (Sum.inl 346, -58466748000), (Sum.inl 347, -24456750000), (Sum.inl 348, 106974828000), (Sum.inl 349, 24456750000), (Sum.inl 350, -106974828000), (Sum.inl 354, -23917920000), (Sum.inl 373, 16841002200), (Sum.inl 377, 23760280000), (Sum.inl 384, 20443142000), (Sum.inl 385, 70687015000), (Sum.inl 394, -12248001600), (Sum.inl 395, 16841002200), (Sum.inl 402, -24210780000), (Sum.inl 405, 141744323200), (Sum.inl 406, -21695798400), (Sum.inl 409, -4403787000), (Sum.inl 410, 9117984000), (Sum.inl 420, 11834438400), (Sum.inl 452, -3033532800)]

theorem originalBlockCheck15 : originalBlock15 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock15 keyMomentRows) := by decide +kernel

theorem originalBlockEval15 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock15 x =
      Integer.Sparse.eval keyPolynomialBlock15 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck15, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
