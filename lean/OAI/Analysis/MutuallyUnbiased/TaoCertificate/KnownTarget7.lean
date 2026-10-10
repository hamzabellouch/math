import OAI.Analysis.MutuallyUnbiased.Tao.TaoTarget

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams7 : List (Charge × Coeff) := [(![1, 0, 1, 0, 0, -2], (36, 36)), (![1, 1, -2, 0, 0, 0], (0, -36)), (![1, 1, 0, -2, 0, 0], (36, 36)), (![1, 1, 0, 0, -2, 0], (36, 36)), (![1, 1, 0, 0, 0, -2], (0, -36)), (![2, -1, -1, 0, 0, 0], (36, 36)), (![2, -1, 0, -1, 0, 0], (0, -36)), (![2, -1, 0, 0, -1, 0], (0, -36)), (![2, -1, 0, 0, 0, -1], (36, 36)), (![2, 0, -1, -1, 0, 0], (36, 36)), (![2, 0, -1, 0, -1, 0], (0, -36)), (![2, 0, -1, 0, 0, -1], (0, -36)), (![2, 0, 0, -1, -1, 0], (36, 36)), (![2, 0, 0, -1, 0, -1], (0, -36)), (![2, 0, 0, 0, -1, -1], (36, 36))]

def knownTarget7 : Sparse := [([0, 1, 0, 1, 0, 0, -2], 36), ([0, 1, 1, 0, -2, 0, 0], 36), ([0, 1, 1, 0, 0, -2, 0], 36), ([0, 2, -1, -1, 0, 0, 0], 36), ([0, 2, -1, 0, 0, 0, -1], 36), ([0, 2, 0, -1, -1, 0, 0], 36), ([0, 2, 0, 0, -1, -1, 0], 36), ([0, 2, 0, 0, 0, -1, -1], 36), ([1, 1, 0, 1, 0, 0, -2], 36), ([1, 1, 1, -2, 0, 0, 0], -36), ([1, 1, 1, 0, -2, 0, 0], 36), ([1, 1, 1, 0, 0, -2, 0], 36), ([1, 1, 1, 0, 0, 0, -2], -36), ([1, 2, -1, -1, 0, 0, 0], 36), ([1, 2, -1, 0, -1, 0, 0], -36), ([1, 2, -1, 0, 0, -1, 0], -36), ([1, 2, -1, 0, 0, 0, -1], 36), ([1, 2, 0, -1, -1, 0, 0], 36), ([1, 2, 0, -1, 0, -1, 0], -36), ([1, 2, 0, -1, 0, 0, -1], -36), ([1, 2, 0, 0, -1, -1, 0], 36), ([1, 2, 0, 0, -1, 0, -1], -36), ([1, 2, 0, 0, 0, -1, -1], 36)]

theorem knownTarget7_checked : normalize (knownTerms knownParams7) = knownTarget7 := by
  decide +kernel

theorem knownParams7_valid : knownParams7.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (108, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget7_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget7 (momentValues f) = -54 := by
  rw [← knownTarget7_checked, eval_normalize,
    eval_knownTerms f hf knownParams7 (108) knownParams7_valid]
  norm_num [knownParams7]

end MUB6.TaoCertificate

end OAI
