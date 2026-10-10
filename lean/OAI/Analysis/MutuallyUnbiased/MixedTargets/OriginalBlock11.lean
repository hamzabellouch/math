import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock11 : Integer.Sparse (Fin 2886) := [(352, 25944217680), (353, -4891350000), (354, -4593000600), (355, 34130795040), (356, 7681584000), (357, 72408693800), (358, 51916555200), (359, 12511067520), (360, -9829123200), (361, -40223205600), (362, -4096241280), (363, -4891350000), (364, -4593000600), (365, -655456000), (366, -7865472000), (367, -7681584000), (368, 984853440), (369, -32363434400), (370, 8357064000), (371, -31096581600), (372, 10438497600), (373, 4891350000), (374, 5817800760), (375, 689808000), (376, -2879009760), (377, 3021984000), (378, 3440836800), (379, 26916001920), (380, -8256782016), (381, -38337686400), (382, -85045968720), (383, -62829660000)]

def originalBlock11 : Integer.Sparse OriginalKey := [(Sum.inl 139, 52192488000), (Sum.inl 145, -155482908000), (Sum.inl 148, 4924267200), (Sum.inl 165, -41283910080), (Sum.inl 177, 17204184000), (Sum.inl 238, 134580009600), (Sum.inl 246, 15109920000), (Sum.inl 263, -206083480800), (Sum.inl 264, 3449040000), (Sum.inl 269, 170653975200), (Sum.inl 322, 24456750000), (Sum.inl 346, 129721088400), (Sum.inl 364, 62555337600), (Sum.inl 373, 29089003800), (Sum.inl 377, 41785320000), (Sum.inl 384, -123409252000), (Sum.inl 391, -38407920000), (Sum.inl 440, -20481206400), (Sum.inl 443, -201116028000), (Sum.inl 458, -314148300000), (Sum.inl 463, -425229843600), (Sum.inl 468, 362043469000), (Sum.inl 476, -24456750000), (Sum.inl 478, -39327360000), (Sum.inl 480, -24456750000), (Sum.inl 481, -49145616000), (Sum.inl 484, -22965003000), (Sum.inl 489, -3277280000), (Sum.inl 491, 259582776000), (Sum.inl 492, -22965003000)]

theorem originalBlockCheck11 : originalBlock11 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock11 keyMomentRows) := by decide +kernel

theorem originalBlockEval11 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock11 x =
      Integer.Sparse.eval keyPolynomialBlock11 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck11, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
