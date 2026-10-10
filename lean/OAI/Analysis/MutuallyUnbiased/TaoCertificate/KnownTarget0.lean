import OAI.Analysis.MutuallyUnbiased.Tao.TaoTarget

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams0 : List (Charge × Coeff) := [(![-2, 0, 0, 0, 1, 1], (0, -36)), (![-2, 0, 0, 1, 0, 1], (36, 36)), (![-2, 0, 0, 1, 1, 0], (0, -36)), (![-2, 0, 1, 0, 0, 1], (36, 36)), (![-2, 0, 1, 0, 1, 0], (36, 36)), (![-2, 0, 1, 1, 0, 0], (0, -36)), (![-2, 1, 0, 0, 0, 1], (0, -36)), (![-2, 1, 0, 0, 1, 0], (36, 36)), (![-2, 1, 0, 1, 0, 0], (36, 36)), (![-2, 1, 1, 0, 0, 0], (0, -36)), (![-1, -1, 0, 0, 0, 2], (36, 36)), (![-1, -1, 0, 0, 2, 0], (0, -36)), (![-1, -1, 0, 2, 0, 0], (0, -36)), (![-1, -1, 2, 0, 0, 0], (36, 36)), (![-1, 0, -1, 0, 0, 2], (0, -36))]

def knownTarget0 : Sparse := [([0, -2, 0, 0, 1, 0, 1], 36), ([0, -2, 0, 1, 0, 0, 1], 36), ([0, -2, 0, 1, 0, 1, 0], 36), ([0, -2, 1, 0, 0, 1, 0], 36), ([0, -2, 1, 0, 1, 0, 0], 36), ([0, -1, -1, 0, 0, 0, 2], 36), ([0, -1, -1, 2, 0, 0, 0], 36), ([1, -2, 0, 0, 0, 1, 1], -36), ([1, -2, 0, 0, 1, 0, 1], 36), ([1, -2, 0, 0, 1, 1, 0], -36), ([1, -2, 0, 1, 0, 0, 1], 36), ([1, -2, 0, 1, 0, 1, 0], 36), ([1, -2, 0, 1, 1, 0, 0], -36), ([1, -2, 1, 0, 0, 0, 1], -36), ([1, -2, 1, 0, 0, 1, 0], 36), ([1, -2, 1, 0, 1, 0, 0], 36), ([1, -2, 1, 1, 0, 0, 0], -36), ([1, -1, -1, 0, 0, 0, 2], 36), ([1, -1, -1, 0, 0, 2, 0], -36), ([1, -1, -1, 0, 2, 0, 0], -36), ([1, -1, -1, 2, 0, 0, 0], 36), ([1, -1, 0, -1, 0, 0, 2], -36)]

theorem knownTarget0_checked : normalize (knownTerms knownParams0) = knownTarget0 := by
  decide +kernel

theorem knownParams0_valid : knownParams0.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (108, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget0_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget0 (momentValues f) = -54 := by
  rw [← knownTarget0_checked, eval_normalize,
    eval_knownTerms f hf knownParams0 (108) knownParams0_valid]
  norm_num [knownParams0]

end MUB6.TaoCertificate

end OAI
