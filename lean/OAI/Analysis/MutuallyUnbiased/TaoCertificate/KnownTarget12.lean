import OAI.Analysis.MutuallyUnbiased.Tao.TaoTarget

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams12 : List (Charge × Coeff) := [(![1, -1, -1, 0, 0, 1], (-144, 0)), (![1, -1, -1, 0, 1, 0], (144, 144)), (![1, -1, -1, 1, 0, 0], (-144, 0)), (![1, -1, 0, -1, 0, 1], (-144, 0)), (![1, -1, 0, -1, 1, 0], (-144, 0)), (![1, -1, 0, 0, -1, 1], (0, -144)), (![1, -1, 0, 0, 1, -1], (-144, 0)), (![1, -1, 0, 1, -1, 0], (-144, 0)), (![1, -1, 0, 1, 0, -1], (144, 144)), (![1, -1, 1, -1, 0, 0], (0, -144)), (![1, -1, 1, 0, -1, 0], (-144, 0)), (![1, -1, 1, 0, 0, -1], (-144, 0)), (![1, 0, -1, -1, 0, 1], (144, 144)), (![1, 0, -1, -1, 1, 0], (-144, 0)), (![1, 0, -1, 0, -1, 1], (-144, 0))]

def knownTarget12 : Sparse := [([0, 1, -1, -1, 0, 0, 1], -144), ([0, 1, -1, -1, 0, 1, 0], 144), ([0, 1, -1, -1, 1, 0, 0], -144), ([0, 1, -1, 0, -1, 0, 1], -144), ([0, 1, -1, 0, -1, 1, 0], -144), ([0, 1, -1, 0, 0, 1, -1], -144), ([0, 1, -1, 0, 1, -1, 0], -144), ([0, 1, -1, 0, 1, 0, -1], 144), ([0, 1, -1, 1, 0, -1, 0], -144), ([0, 1, -1, 1, 0, 0, -1], -144), ([0, 1, 0, -1, -1, 0, 1], 144), ([0, 1, 0, -1, -1, 1, 0], -144), ([0, 1, 0, -1, 0, -1, 1], -144), ([1, 1, -1, -1, 0, 1, 0], 144), ([1, 1, -1, 0, 0, -1, 1], -144), ([1, 1, -1, 0, 1, 0, -1], 144), ([1, 1, -1, 1, -1, 0, 0], -144), ([1, 1, 0, -1, -1, 0, 1], 144)]

theorem knownTarget12_checked : normalize (knownTerms knownParams12) = knownTarget12 := by
  decide +kernel

theorem knownParams12_valid : knownParams12.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (-432, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget12_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget12 (momentValues f) = 216 := by
  rw [← knownTarget12_checked, eval_normalize,
    eval_knownTerms f hf knownParams12 (-432) knownParams12_valid]
  norm_num [knownParams12]

end MUB6.TaoCertificate

end OAI
