import OAI.Analysis.MutuallyUnbiased.Tao.TaoTarget

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams13 : List (Charge × Coeff) := [(![1, 0, -1, 0, 1, -1], (-144, 0)), (![1, 0, -1, 1, -1, 0], (0, -144)), (![1, 0, -1, 1, 0, -1], (-144, 0)), (![1, 0, 0, -1, -1, 1], (-144, 0)), (![1, 0, 0, -1, 1, -1], (0, -144)), (![1, 0, 0, 1, -1, -1], (-144, 0)), (![1, 0, 1, -1, -1, 0], (-144, 0)), (![1, 0, 1, -1, 0, -1], (-144, 0)), (![1, 0, 1, 0, -1, -1], (144, 144)), (![1, 1, -1, -1, 0, 0], (-144, 0)), (![1, 1, -1, 0, -1, 0], (-144, 0)), (![1, 1, -1, 0, 0, -1], (0, -144)), (![1, 1, 0, -1, -1, 0], (144, 144)), (![1, 1, 0, -1, 0, -1], (-144, 0)), (![1, 1, 0, 0, -1, -1], (-144, 0))]

def knownTarget13 : Sparse := [([0, 1, 0, -1, 0, 1, -1], -144), ([0, 1, 0, -1, 1, 0, -1], -144), ([0, 1, 0, 0, -1, -1, 1], -144), ([0, 1, 0, 0, 1, -1, -1], -144), ([0, 1, 0, 1, -1, -1, 0], -144), ([0, 1, 0, 1, -1, 0, -1], -144), ([0, 1, 0, 1, 0, -1, -1], 144), ([0, 1, 1, -1, -1, 0, 0], -144), ([0, 1, 1, -1, 0, -1, 0], -144), ([0, 1, 1, 0, -1, -1, 0], 144), ([0, 1, 1, 0, -1, 0, -1], -144), ([0, 1, 1, 0, 0, -1, -1], -144), ([1, 1, 0, -1, 1, -1, 0], -144), ([1, 1, 0, 0, -1, 1, -1], -144), ([1, 1, 0, 1, 0, -1, -1], 144), ([1, 1, 1, -1, 0, 0, -1], -144), ([1, 1, 1, 0, -1, -1, 0], 144)]

theorem knownTarget13_checked : normalize (knownTerms knownParams13) = knownTarget13 := by
  decide +kernel

theorem knownParams13_valid : knownParams13.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (-432, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget13_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget13 (momentValues f) = 216 := by
  rw [← knownTarget13_checked, eval_normalize,
    eval_knownTerms f hf knownParams13 (-432) knownParams13_valid]
  norm_num [knownParams13]

end MUB6.TaoCertificate

end OAI
