import OAI.Analysis.MutuallyUnbiased.Tao.TaoTarget

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams5 : List (Charge × Coeff) := [(![0, 1, 0, -2, 0, 1], (0, -36)), (![0, 1, 0, -2, 1, 0], (0, -36)), (![0, 1, 0, 0, -2, 1], (36, 36)), (![0, 1, 0, 0, 1, -2], (36, 36)), (![0, 1, 0, 1, -2, 0], (0, -36)), (![0, 1, 0, 1, 0, -2], (0, -36)), (![0, 1, 1, -2, 0, 0], (36, 36)), (![0, 1, 1, 0, -2, 0], (0, -36)), (![0, 1, 1, 0, 0, -2], (36, 36)), (![0, 2, -1, -1, 0, 0], (0, -36)), (![0, 2, -1, 0, -1, 0], (36, 36)), (![0, 2, -1, 0, 0, -1], (0, -36)), (![0, 2, 0, -1, -1, 0], (36, 36)), (![0, 2, 0, -1, 0, -1], (36, 36)), (![0, 2, 0, 0, -1, -1], (0, -36))]

def knownTarget5 : Sparse := [([0, 0, 1, 0, 0, -2, 1], 36), ([0, 0, 1, 0, 0, 1, -2], 36), ([0, 0, 1, 1, -2, 0, 0], 36), ([0, 0, 1, 1, 0, 0, -2], 36), ([0, 0, 2, -1, 0, -1, 0], 36), ([0, 0, 2, 0, -1, -1, 0], 36), ([0, 0, 2, 0, -1, 0, -1], 36), ([1, 0, 1, 0, -2, 0, 1], -36), ([1, 0, 1, 0, -2, 1, 0], -36), ([1, 0, 1, 0, 0, -2, 1], 36), ([1, 0, 1, 0, 0, 1, -2], 36), ([1, 0, 1, 0, 1, -2, 0], -36), ([1, 0, 1, 0, 1, 0, -2], -36), ([1, 0, 1, 1, -2, 0, 0], 36), ([1, 0, 1, 1, 0, -2, 0], -36), ([1, 0, 1, 1, 0, 0, -2], 36), ([1, 0, 2, -1, -1, 0, 0], -36), ([1, 0, 2, -1, 0, -1, 0], 36), ([1, 0, 2, -1, 0, 0, -1], -36), ([1, 0, 2, 0, -1, -1, 0], 36), ([1, 0, 2, 0, -1, 0, -1], 36), ([1, 0, 2, 0, 0, -1, -1], -36)]

theorem knownTarget5_checked : normalize (knownTerms knownParams5) = knownTarget5 := by
  decide +kernel

theorem knownParams5_valid : knownParams5.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (108, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget5_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget5 (momentValues f) = -54 := by
  rw [← knownTarget5_checked, eval_normalize,
    eval_knownTerms f hf knownParams5 (108) knownParams5_valid]
  norm_num [knownParams5]

end MUB6.TaoCertificate

end OAI
