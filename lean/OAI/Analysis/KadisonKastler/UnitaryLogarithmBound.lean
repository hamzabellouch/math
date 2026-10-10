import OAI.Analysis.KadisonKastler.Algebra
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace OAI

/-! # A controlled self-adjoint logarithm near the identity -/

namespace KadisonKastler

open scoped Real

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_argSelfAdjoint_le_two_mul (u : unitary (H →L[ℂ] H))
    (hu : ‖(u : H →L[ℂ] H) - 1‖ < 2) :
    ‖Unitary.argSelfAdjoint u‖ ≤ 2 * ‖(u : H →L[ℂ] H) - 1‖ := by
  let θ := ‖Unitary.argSelfAdjoint u‖
  let d := ‖(u : H →L[ℂ] H) - 1‖
  have hθ : 0 ≤ θ := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hθpi : θ ≤ Real.pi := Unitary.norm_argSelfAdjoint_le_pi u
  have hc := Real.cos_le_one_sub_mul_cos_sq
    (x := θ) (by rwa [abs_of_nonneg hθ])
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hc' : Real.pi ^ 2 * Real.cos θ ≤ Real.pi ^ 2 - 2 * θ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hc hpi.le
    convert h using 1; field_simp
  have heq : 2 * (1 - Real.cos θ) = d ^ 2 :=
    Unitary.two_mul_one_sub_cos_norm_argSelfAdjoint hu
  have heq' := congrArg (fun r : ℝ => Real.pi ^ 2 * r) heq
  have hb : 4 * θ ^ 2 ≤ Real.pi ^ 2 * d ^ 2 := by nlinarith
  have hpi4 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hb' := mul_le_mul_of_nonneg_right hpi4 (sq_nonneg d)
  change θ ≤ 2 * d
  nlinarith

theorem exists_small_selfAdjoint_log (u : unitary (H →L[ℂ] H))
    (hu : ‖(u : H →L[ℂ] H) - 1‖ < 2) :
    ∃ h : selfAdjoint (H →L[ℂ] H), selfAdjoint.expUnitary h = u ∧
      ‖h‖ ≤ 2 * ‖(u : H →L[ℂ] H) - 1‖ :=
  ⟨Unitary.argSelfAdjoint u, expUnitary_argSelfAdjoint hu,
    norm_argSelfAdjoint_le_two_mul u hu⟩

end

end KadisonKastler

end OAI
