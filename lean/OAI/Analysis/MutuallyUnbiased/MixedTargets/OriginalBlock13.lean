import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock13 : Integer.Sparse (Fin 2886) := [(416, 31096581600), (417, -4891350000), (418, -4593000600), (419, 2565312000), (420, 22659036000), (421, 3021984000), (422, -15448158720), (423, 4608692640), (424, 28903210080), (425, -30639798720), (426, 16865093280), (427, 364979040), (428, -6472454400), (429, -4157069760), (430, -10027419840), (431, -9536209920), (432, -12460468800), (433, 12702349440), (434, 48085286400), (435, -12705079680), (436, 9079309440), (437, -2969668800), (438, -12702349440), (439, -6052872960), (440, 6340708800), (441, -31525516800), (442, -11702125440), (443, 82138442400), (444, -11702125440), (445, 8919414720), (446, 8378760000), (447, -23681979360)]

def originalBlock13 : Integer.Sparse OriginalKey := [(Sum.inl 15, -77240793600), (Sum.inl 17, 1824895200), (Sum.inl 36, 15109920000), (Sum.inl 103, 12826560000), (Sum.inl 116, 84325466400), (Sum.inl 130, 155482908000), (Sum.inl 149, 113295180000), (Sum.inl 168, 23043463200), (Sum.inl 171, 41893800000), (Sum.inl 173, -14848344000), (Sum.inl 179, -63511747200), (Sum.inl 182, 240426432000), (Sum.inl 185, -47681049600), (Sum.inl 209, 31703544000), (Sum.inl 223, -30264364800), (Sum.inl 235, -63525398400), (Sum.inl 248, 63511747200), (Sum.inl 251, -50137099200), (Sum.inl 261, 45396547200), (Sum.inl 268, -62302344000), (Sum.inl 269, -20785348800), (Sum.inl 270, -32362272000), (Sum.inl 278, 144516050400), (Sum.inl 279, -153198993600), (Sum.inl 296, -24456750000), (Sum.inl 300, -22965003000), (Sum.inl 412, -157627584000), (Sum.inl 439, -58510627200), (Sum.inl 455, 44597073600), (Sum.inl 467, 410692212000), (Sum.inl 468, -58510627200), (Sum.inl 507, -118409896800)]

theorem originalBlockCheck13 : originalBlock13 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock13 keyMomentRows) := by decide +kernel

theorem originalBlockEval13 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock13 x =
      Integer.Sparse.eval keyPolynomialBlock13 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck13, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
