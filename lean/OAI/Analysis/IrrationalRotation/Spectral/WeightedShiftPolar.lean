import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftPowers
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

namespace OAI

noncomputable section
open scoped ENNReal InnerProductSpace ComplexOrder
namespace Invariant233.WeightedShift.PolarSupport

local instance hilbertNontrivial : Nontrivial Hilbert := by
  refine ⟨⟨0, lp.single 2 0 1, ?_⟩⟩
  intro h
  have hh := congrArg (fun ξ : Hilbert => ξ 0) h
  simp at hh

local instance weightedShiftPolarRealModule : Module ℝ (Hilbert →L[ℂ] Hilbert) :=
  Module.complexToReal (Hilbert →L[ℂ] Hilbert)

local instance weightedShiftPolarFunctionalCalculus : NonUnitalContinuousFunctionalCalculus ℝ
    (Hilbert →L[ℂ] Hilbert) IsSelfAdjoint := by
  infer_instance

theorem diagonal_operator_injective (w : Weight) (hw : ∀ k, w k ≠ 0) :
    Function.Injective (diagonal w) := by
  intro ξ η h
  ext k
  have hk := congrArg (fun ζ : Hilbert => ζ k) h
  exact mul_left_cancel₀ (hw k) hk

theorem operator_injective (w : Weight) (hw : ∀ k, w k ≠ 0) :
    Function.Injective (operator w) :=
  (shift 1).injective.comp (diagonal_operator_injective w hw)

private theorem star_diagonal_polar (w : Weight) :
    star (diagonal w) = diagonal (star w) := by
  ext ξ k
  have hsingle : diagonal w (lp.single 2 k 1) = lp.single 2 k (w k) := by
    ext j
    by_cases hj : j = k
    · subst j; simp
    · simp [lp.single_apply, hj]
  have h := (diagonal w).adjoint_inner_right (lp.single 2 k 1) ξ
  rw [hsingle, lp.inner_single_left, lp.inner_single_left] at h
  simpa [ContinuousLinearMap.star_eq_adjoint, lp.star_apply, mul_comm] using h

private theorem diagonal_mul_polar (w v : Weight) :
    diagonal (w * v) = diagonal w * diagonal v := by
  ext ξ k
  simp [mul_assoc]

def sqrtRealWeight (w : Weight) : Weight :=
  ⟨fun k => (Real.sqrt (w k).re : ℂ), memℓp_infty <| by
    refine ⟨Real.sqrt ‖w‖, ?_⟩
    rintro r ⟨k, rfl⟩
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((Complex.re_le_norm _).trans
      (lp.norm_apply_le_norm (by simp) w k))⟩

theorem star_sqrtRealWeight_mul (w : Weight) (hw : ∀ k, 0 ≤ w k) :
    star (sqrtRealWeight w) * sqrtRealWeight w = w := by
  ext k
  have hk := Complex.nonneg_iff.mp (hw k)
  apply Complex.ext
  · simp [sqrtRealWeight, Real.mul_self_sqrt hk.1]
  · simpa [sqrtRealWeight, lp.star_apply] using hk.2

theorem diagonal_nonneg (w : Weight) (hw : ∀ k, 0 ≤ w k) :
    0 ≤ diagonal w := by
  rw [← star_sqrtRealWeight_mul w hw, diagonal_mul_polar, ← star_diagonal_polar]
  exact star_mul_self_nonneg _

theorem star_shift_mul_shift (n : ℤ) :
    star (shift n : Hilbert →L[ℂ] Hilbert) * (shift n : Hilbert →L[ℂ] Hilbert) = 1 := by
  rw [ContinuousLinearMap.star_eq_adjoint, (shift n).adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro ξ
  exact (shift n).symm_apply_apply ξ

theorem shift_mul_star_shift (n : ℤ) :
    (shift n : Hilbert →L[ℂ] Hilbert) * star (shift n : Hilbert →L[ℂ] Hilbert) = 1 := by
  rw [ContinuousLinearMap.star_eq_adjoint, (shift n).adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro ξ
  exact (shift n).apply_symm_apply ξ

theorem shift_mem_unitary (n : ℤ) :
    (shift n : Hilbert →L[ℂ] Hilbert) ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  Unitary.mem_iff.mpr ⟨star_shift_mul_shift n, shift_mul_star_shift n⟩

theorem abs_operator_eq_abs_diagonal (w : Weight) :
    CFC.abs (operator w) = CFC.abs (diagonal w) := by
  have hgram : star (operator w) * operator w = star (diagonal w) * diagonal w := by
    change star ((shift 1 : Hilbert →L[ℂ] Hilbert) * diagonal w) *
      ((shift 1 : Hilbert →L[ℂ] Hilbert) * diagonal w) = _
    rw [star_mul]
    calc
      (star (diagonal w) * star (shift 1 : Hilbert →L[ℂ] Hilbert)) *
          ((shift 1 : Hilbert →L[ℂ] Hilbert) * diagonal w) =
          star (diagonal w) *
            (star (shift 1 : Hilbert →L[ℂ] Hilbert) *
              (shift 1 : Hilbert →L[ℂ] Hilbert)) * diagonal w := by
                simp only [mul_assoc]
      _ = star (diagonal w) * diagonal w := by rw [star_shift_mul_shift]; simp
  exact congrArg CFC.sqrt hgram

theorem abs_operator (w : Weight) (hw : ∀ k, 0 ≤ w k) :
    CFC.abs (operator w) = diagonal w := by
  rw [abs_operator_eq_abs_diagonal, CFC.abs_of_nonneg _ (diagonal_nonneg w hw)]

theorem operator_eq_shift_mul_abs (w : Weight) (hw : ∀ k, 0 ≤ w k) :
    operator w = (shift 1 : Hilbert →L[ℂ] Hilbert) * CFC.abs (operator w) := by
  rw [abs_operator w hw]
  rfl

theorem ker_abs_operator_eq_bot (w : Weight) (hw : ∀ k, 0 < w k) :
    (CFC.abs (operator w)).ker = ⊥ := by
  rw [abs_operator w (fun k => (hw k).le)]
  exact LinearMap.ker_eq_bot.mpr (diagonal_operator_injective w (fun k => (hw k).ne'))

theorem positive_weight_polar_data (w : Weight) (hw : ∀ k, 0 < w k) :
    (shift 1 : Hilbert →L[ℂ] Hilbert) ∈ unitary (Hilbert →L[ℂ] Hilbert) ∧
    0 ≤ diagonal w ∧ CFC.abs (operator w) = diagonal w ∧
    (CFC.abs (operator w)).ker = ⊥ ∧
    operator w = (shift 1 : Hilbert →L[ℂ] Hilbert) * CFC.abs (operator w) :=
  ⟨shift_mem_unitary 1, diagonal_nonneg w (fun k => (hw k).le),
    abs_operator w (fun k => (hw k).le), ker_abs_operator_eq_bot w hw,
    operator_eq_shift_mul_abs w (fun k => (hw k).le)⟩

end Invariant233.WeightedShift.PolarSupport

end

end OAI
