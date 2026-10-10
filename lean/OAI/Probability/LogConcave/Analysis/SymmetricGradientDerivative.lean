import Mathlib
import OAI.Probability.LogConcave.Model
import OAI.Probability.LogConcave.Sampling.ContinuousFirstOrderReply

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
open scoped RealInnerProductSpace

theorem ContDiff.isSymmetric_gradient_derivative {d : ℕ} {V : Point d → ℝ}
    (hV : ContDiff ℝ 2 V) (x : Point d) :
    (fderiv ℝ (gradient V) x).IsSymmetric := by
  have hg : ContDiff ℝ 1 (gradient V) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp
      (hV.fderiv_right (by norm_num))
  have hd := ((InnerProductSpace.toDual ℝ (Point d)).hasFDerivAt).comp x
    ((hg.differentiable (by norm_num) x).hasFDerivAt)
  have he : fderiv ℝ (fderiv ℝ V) x =
      (InnerProductSpace.toDual ℝ (Point d)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (gradient V) x) := by
    have hid := toDual_comp_gradient (𝕜 := ℝ) (f := V)
    rw [hid] at hd
    exact hd.fderiv
  have hs := (hV.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num [minSmoothness])
  intro v w
  have h := hs.eq v w
  rw [he] at h
  change inner ℝ ((fderiv ℝ (gradient V) x) v) w =
    inner ℝ v ((fderiv ℝ (gradient V) x) w)
  conv_rhs => rw [real_inner_comm]
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, InnerProductSpace.toDual_apply_apply] using h

theorem Admissible.gradient_lipschitz {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : LipschitzWith 2 (gradient V) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (hV.contDiff_gradient.differentiable (by norm_num))
  intro x
  change ‖fderiv ℝ (gradient V) x‖ ≤ (2 : ℝ)
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient
    (fderiv ℝ (gradient V) x) (ContDiff.isSymmetric_gradient_derivative hV.smooth x)]
  apply ciSup_le
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  rw [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm]
  simp only [RCLike.re_to_real]
  rw [abs_of_nonneg (div_nonneg ((sq_nonneg ‖v‖).trans (hV.hessian_bounds x v).1)
    (sq_nonneg ‖v‖)), div_le_iff₀ hn]
  exact (hV.hessian_bounds x v).2

theorem Admissible.gradient_norm_le {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) (x : Point d) : ‖gradient V x‖ ≤ 2 * ‖x‖ := by
  simpa [dist_eq_norm, hV.gradient_zero] using hV.gradient_lipschitz.dist_le_mul x 0

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
