import OAI.NumberTheory.CubicMoment.Estimates.HeckeDualContour

namespace OAI

/-! The exact `sqrt(Z/J)` normalization of a retained dual norm block.
The normalized coefficients are independent of the character conductor. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma positive_cpow_phase {x : ℝ} (hx : 0 < x) (σ u : ℝ) :
    (x:ℂ)^((σ:ℂ)+(u:ℂ)*Complex.I) = (x^σ:ℝ)*mellinPhase u x := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le,Real.rpow_def_of_pos hx,Complex.ofReal_exp]
  unfold mellinPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma dual_dyad_weight_identity {J x : ℝ} (hJ : 0 < J) (hx : 0 < x) :
    x^(-(1/2:ℝ)) = J^(-(1/2:ℝ))*(J/x)^(1/2:ℝ) := by
  rw [Real.div_rpow hJ.le hx.le,Real.rpow_neg hJ.le,Real.rpow_neg hx.le]
  field_simp [(Real.rpow_pos_of_pos hJ (1/2:ℝ)).ne']

lemma dual_dyad_weight_le_one {J x : ℝ} (hJ : 0 < J) (hx : J ≤ x) :
    (J/x)^(1/2:ℝ) ≤ 1 := by
  apply Real.rpow_le_one
  · exact div_nonneg hJ.le (hJ.le.trans hx)
  · exact (div_le_one (hJ.trans_le hx)).mpr hx
  · norm_num

/-- Extracting the inverse square-root dyadic length changes only the
fixed norm coefficients; the character remains in the same polynomial. -/
theorem finite_dual_dyad_rescale {ι : Type*} (S : Finset ι) (a : ι → ℂ)
    (N : ι → ℝ) {J : ℝ} (hJ : 0 < J) (hN : ∀ i ∈ S, 0 < N i) (u : ℝ) :
    finiteNormDirichlet S a N ((1/2:ℂ)-(u:ℂ)*Complex.I) =
      (J^(-(1/2:ℝ)):ℝ)*∑ i ∈ S,
        (a i*((J/N i)^(1/2:ℝ):ℝ))*mellinPhase u (N i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : -((1/2:ℂ)-(u:ℂ)*Complex.I) = ((-(1/2:ℝ)):ℂ)+(u:ℂ)*Complex.I := by
    push_cast
    ring
  change a i*(N i:ℂ)^(-((1/2:ℂ)-(u:ℂ)*Complex.I)) = _
  rw [he,← Complex.ofReal_neg,positive_cpow_phase (hN i hi) (-(1/2:ℝ)) u,dual_dyad_weight_identity hJ (hN i hi)]
  push_cast
  ring

lemma norm_dual_dyad_coefficient_le {J x : ℝ} (hJ : 0 < J) (hx : J ≤ x) (a : ℂ) :
    ‖a*((J/x)^(1/2:ℝ):ℝ)‖ ≤ ‖a‖ := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (div_nonneg hJ.le (hJ.le.trans hx)) _)]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _) (dual_dyad_weight_le_one hJ hx)

end CubicFirstMoment

end

end OAI
