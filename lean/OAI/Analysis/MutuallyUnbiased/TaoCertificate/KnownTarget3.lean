import OAI.Analysis.MutuallyUnbiased.Tao.TaoTarget

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams3 : List (Charge × Coeff) := [(![0, -1, 2, -1, 0, 0], (0, -36)), (![0, -1, 2, 0, -1, 0], (36, 36)), (![0, -1, 2, 0, 0, -1], (0, -36)), (![0, 0, -2, 0, 1, 1], (0, -36)), (![0, 0, -2, 1, 0, 1], (0, -36)), (![0, 0, -2, 1, 1, 0], (36, 36)), (![0, 0, -1, -1, 0, 2], (36, 36)), (![0, 0, -1, -1, 2, 0], (0, -36)), (![0, 0, -1, 0, -1, 2], (36, 36)), (![0, 0, -1, 0, 2, -1], (36, 36)), (![0, 0, -1, 2, -1, 0], (0, -36)), (![0, 0, -1, 2, 0, -1], (36, 36)), (![0, 0, 0, -2, 1, 1], (36, 36)), (![0, 0, 0, -1, -1, 2], (0, -36)), (![0, 0, 0, -1, 2, -1], (0, -36))]

def knownTarget3 : Sparse := [([0, 0, -1, 2, 0, -1, 0], 36), ([0, 0, 0, -2, 1, 1, 0], 36), ([0, 0, 0, -1, -1, 0, 2], 36), ([0, 0, 0, -1, 0, -1, 2], 36), ([0, 0, 0, -1, 0, 2, -1], 36), ([0, 0, 0, -1, 2, 0, -1], 36), ([0, 0, 0, 0, -2, 1, 1], 36), ([1, 0, -1, 2, -1, 0, 0], -36), ([1, 0, -1, 2, 0, -1, 0], 36), ([1, 0, -1, 2, 0, 0, -1], -36), ([1, 0, 0, -2, 0, 1, 1], -36), ([1, 0, 0, -2, 1, 0, 1], -36), ([1, 0, 0, -2, 1, 1, 0], 36), ([1, 0, 0, -1, -1, 0, 2], 36), ([1, 0, 0, -1, -1, 2, 0], -36), ([1, 0, 0, -1, 0, -1, 2], 36), ([1, 0, 0, -1, 0, 2, -1], 36), ([1, 0, 0, -1, 2, -1, 0], -36), ([1, 0, 0, -1, 2, 0, -1], 36), ([1, 0, 0, 0, -2, 1, 1], 36), ([1, 0, 0, 0, -1, -1, 2], -36), ([1, 0, 0, 0, -1, 2, -1], -36)]

theorem knownTarget3_checked : normalize (knownTerms knownParams3) = knownTarget3 := by
  decide +kernel

theorem knownParams3_valid : knownParams3.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (108, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget3_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget3 (momentValues f) = -54 := by
  rw [← knownTarget3_checked, eval_normalize,
    eval_knownTerms f hf knownParams3 (108) knownParams3_valid]
  norm_num [knownParams3]

end MUB6.TaoCertificate

end OAI
