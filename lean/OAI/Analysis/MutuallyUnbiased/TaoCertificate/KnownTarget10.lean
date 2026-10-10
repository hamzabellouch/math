import OAI.Analysis.MutuallyUnbiased.Tao.TaoTarget

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams10 : List (Charge × Coeff) := [(![0, -1, -1, 0, 1, 1], (-144, 0)), (![0, -1, -1, 1, 0, 1], (0, -144)), (![0, -1, -1, 1, 1, 0], (-144, 0)), (![0, -1, 0, -1, 1, 1], (144, 144)), (![0, -1, 0, 1, -1, 1], (-144, 0)), (![0, -1, 0, 1, 1, -1], (-144, 0)), (![0, -1, 1, -1, 0, 1], (-144, 0)), (![0, -1, 1, -1, 1, 0], (-144, 0)), (![0, -1, 1, 0, -1, 1], (-144, 0)), (![0, -1, 1, 0, 1, -1], (0, -144)), (![0, -1, 1, 1, -1, 0], (144, 144)), (![0, -1, 1, 1, 0, -1], (-144, 0)), (![0, 0, -1, -1, 1, 1], (-144, 0)), (![0, 0, -1, 1, -1, 1], (-144, 0)), (![0, 0, -1, 1, 1, -1], (144, 144))]

def knownTarget10 : Sparse := [([0, 0, -1, -1, 0, 1, 1], -144), ([0, 0, -1, -1, 1, 1, 0], -144), ([0, 0, -1, 0, -1, 1, 1], 144), ([0, 0, -1, 0, 1, -1, 1], -144), ([0, 0, -1, 0, 1, 1, -1], -144), ([0, 0, -1, 1, -1, 0, 1], -144), ([0, 0, -1, 1, -1, 1, 0], -144), ([0, 0, -1, 1, 0, -1, 1], -144), ([0, 0, -1, 1, 1, -1, 0], 144), ([0, 0, -1, 1, 1, 0, -1], -144), ([0, 0, 0, -1, -1, 1, 1], -144), ([0, 0, 0, -1, 1, -1, 1], -144), ([0, 0, 0, -1, 1, 1, -1], 144), ([1, 0, -1, -1, 1, 0, 1], -144), ([1, 0, -1, 0, -1, 1, 1], 144), ([1, 0, -1, 1, 0, 1, -1], -144), ([1, 0, -1, 1, 1, -1, 0], 144), ([1, 0, 0, -1, 1, 1, -1], 144)]

theorem knownTarget10_checked : normalize (knownTerms knownParams10) = knownTarget10 := by
  decide +kernel

theorem knownParams10_valid : knownParams10.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (-432, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget10_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget10 (momentValues f) = 216 := by
  rw [← knownTarget10_checked, eval_normalize,
    eval_knownTerms f hf knownParams10 (-432) knownParams10_valid]
  norm_num [knownParams10]

end MUB6.TaoCertificate

end OAI
