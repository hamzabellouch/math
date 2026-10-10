import OAI.Analysis.MutuallyUnbiased.Tao.TaoTarget

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams11 : List (Charge × Coeff) := [(![0, 0, 1, -1, -1, 1], (0, -144)), (![0, 0, 1, -1, 1, -1], (-144, 0)), (![0, 0, 1, 1, -1, -1], (-144, 0)), (![0, 1, -1, -1, 0, 1], (-144, 0)), (![0, 1, -1, -1, 1, 0], (0, -144)), (![0, 1, -1, 0, -1, 1], (144, 144)), (![0, 1, -1, 0, 1, -1], (-144, 0)), (![0, 1, -1, 1, -1, 0], (-144, 0)), (![0, 1, -1, 1, 0, -1], (-144, 0)), (![0, 1, 0, -1, -1, 1], (-144, 0)), (![0, 1, 0, -1, 1, -1], (-144, 0)), (![0, 1, 0, 1, -1, -1], (0, -144)), (![0, 1, 1, -1, -1, 0], (-144, 0)), (![0, 1, 1, -1, 0, -1], (144, 144)), (![0, 1, 1, 0, -1, -1], (-144, 0))]

def knownTarget11 : Sparse := [([0, 0, 0, 1, -1, 1, -1], -144), ([0, 0, 0, 1, 1, -1, -1], -144), ([0, 0, 1, -1, -1, 0, 1], -144), ([0, 0, 1, -1, 0, -1, 1], 144), ([0, 0, 1, -1, 0, 1, -1], -144), ([0, 0, 1, -1, 1, -1, 0], -144), ([0, 0, 1, -1, 1, 0, -1], -144), ([0, 0, 1, 0, -1, -1, 1], -144), ([0, 0, 1, 0, -1, 1, -1], -144), ([0, 0, 1, 1, -1, -1, 0], -144), ([0, 0, 1, 1, -1, 0, -1], 144), ([0, 0, 1, 1, 0, -1, -1], -144), ([1, 0, 0, 1, -1, -1, 1], -144), ([1, 0, 1, -1, -1, 1, 0], -144), ([1, 0, 1, -1, 0, -1, 1], 144), ([1, 0, 1, 0, 1, -1, -1], -144), ([1, 0, 1, 1, -1, 0, -1], 144)]

theorem knownTarget11_checked : normalize (knownTerms knownParams11) = knownTarget11 := by
  decide +kernel

theorem knownParams11_valid : knownParams11.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (-432, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget11_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget11 (momentValues f) = 216 := by
  rw [← knownTarget11_checked, eval_normalize,
    eval_knownTerms f hf knownParams11 (-432) knownParams11_valid]
  norm_num [knownParams11]

end MUB6.TaoCertificate

end OAI
