import OAI.Analysis.MutuallyUnbiased.Tao.TaoTarget

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams9 : List (Charge × Coeff) := [(![-1, 0, 1, 0, 1, -1], (-144, 0)), (![-1, 0, 1, 1, -1, 0], (-144, 0)), (![-1, 0, 1, 1, 0, -1], (0, -144)), (![-1, 1, -1, 0, 0, 1], (-144, 0)), (![-1, 1, -1, 0, 1, 0], (-144, 0)), (![-1, 1, -1, 1, 0, 0], (144, 144)), (![-1, 1, 0, -1, 0, 1], (0, -144)), (![-1, 1, 0, -1, 1, 0], (-144, 0)), (![-1, 1, 0, 0, -1, 1], (-144, 0)), (![-1, 1, 0, 0, 1, -1], (144, 144)), (![-1, 1, 0, 1, -1, 0], (-144, 0)), (![-1, 1, 0, 1, 0, -1], (-144, 0)), (![-1, 1, 1, -1, 0, 0], (-144, 0)), (![-1, 1, 1, 0, -1, 0], (0, -144)), (![-1, 1, 1, 0, 0, -1], (-144, 0))]

def knownTarget9 : Sparse := [([0, -1, 0, 1, 0, 1, -1], -144), ([0, -1, 0, 1, 1, -1, 0], -144), ([0, -1, 1, -1, 0, 0, 1], -144), ([0, -1, 1, -1, 0, 1, 0], -144), ([0, -1, 1, -1, 1, 0, 0], 144), ([0, -1, 1, 0, -1, 1, 0], -144), ([0, -1, 1, 0, 0, -1, 1], -144), ([0, -1, 1, 0, 0, 1, -1], 144), ([0, -1, 1, 0, 1, -1, 0], -144), ([0, -1, 1, 0, 1, 0, -1], -144), ([0, -1, 1, 1, -1, 0, 0], -144), ([0, -1, 1, 1, 0, 0, -1], -144), ([1, -1, 0, 1, 1, 0, -1], -144), ([1, -1, 1, -1, 1, 0, 0], 144), ([1, -1, 1, 0, -1, 0, 1], -144), ([1, -1, 1, 0, 0, 1, -1], 144), ([1, -1, 1, 1, 0, -1, 0], -144)]

theorem knownTarget9_checked : normalize (knownTerms knownParams9) = knownTarget9 := by
  decide +kernel

theorem knownParams9_valid : knownParams9.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (-432, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget9_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget9 (momentValues f) = 216 := by
  rw [← knownTarget9_checked, eval_normalize,
    eval_knownTerms f hf knownParams9 (-432) knownParams9_valid]
  norm_num [knownParams9]

end MUB6.TaoCertificate

end OAI
