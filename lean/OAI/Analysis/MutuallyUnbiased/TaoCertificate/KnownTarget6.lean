import OAI.Analysis.MutuallyUnbiased.Tao.TaoTarget

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams6 : List (Charge × Coeff) := [(![1, -2, 0, 0, 0, 1], (0, -36)), (![1, -2, 0, 0, 1, 0], (36, 36)), (![1, -2, 0, 1, 0, 0], (36, 36)), (![1, -2, 1, 0, 0, 0], (0, -36)), (![1, 0, -2, 0, 0, 1], (36, 36)), (![1, 0, -2, 0, 1, 0], (36, 36)), (![1, 0, -2, 1, 0, 0], (0, -36)), (![1, 0, 0, -2, 0, 1], (36, 36)), (![1, 0, 0, -2, 1, 0], (0, -36)), (![1, 0, 0, 0, -2, 1], (0, -36)), (![1, 0, 0, 0, 1, -2], (0, -36)), (![1, 0, 0, 1, -2, 0], (0, -36)), (![1, 0, 0, 1, 0, -2], (36, 36)), (![1, 0, 1, -2, 0, 0], (0, -36)), (![1, 0, 1, 0, -2, 0], (36, 36))]

def knownTarget6 : Sparse := [([0, 1, -2, 0, 0, 1, 0], 36), ([0, 1, -2, 0, 1, 0, 0], 36), ([0, 1, 0, -2, 0, 0, 1], 36), ([0, 1, 0, -2, 0, 1, 0], 36), ([0, 1, 0, 0, -2, 0, 1], 36), ([0, 1, 0, 0, 1, 0, -2], 36), ([0, 1, 0, 1, 0, -2, 0], 36), ([1, 1, -2, 0, 0, 0, 1], -36), ([1, 1, -2, 0, 0, 1, 0], 36), ([1, 1, -2, 0, 1, 0, 0], 36), ([1, 1, -2, 1, 0, 0, 0], -36), ([1, 1, 0, -2, 0, 0, 1], 36), ([1, 1, 0, -2, 0, 1, 0], 36), ([1, 1, 0, -2, 1, 0, 0], -36), ([1, 1, 0, 0, -2, 0, 1], 36), ([1, 1, 0, 0, -2, 1, 0], -36), ([1, 1, 0, 0, 0, -2, 1], -36), ([1, 1, 0, 0, 0, 1, -2], -36), ([1, 1, 0, 0, 1, -2, 0], -36), ([1, 1, 0, 0, 1, 0, -2], 36), ([1, 1, 0, 1, -2, 0, 0], -36), ([1, 1, 0, 1, 0, -2, 0], 36)]

theorem knownTarget6_checked : normalize (knownTerms knownParams6) = knownTarget6 := by
  decide +kernel

theorem knownParams6_valid : knownParams6.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (108, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget6_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget6 (momentValues f) = -54 := by
  rw [← knownTarget6_checked, eval_normalize,
    eval_knownTerms f hf knownParams6 (108) knownParams6_valid]
  norm_num [knownParams6]

end MUB6.TaoCertificate

end OAI
