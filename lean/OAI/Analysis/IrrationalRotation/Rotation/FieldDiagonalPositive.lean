import OAI.Analysis.IrrationalRotation.Rotation.FieldDiagonal
import OAI.Analysis.IrrationalRotation.Spectral.WeightedShiftPolar

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexOrder

namespace Invariant233.WeightedShift

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem fieldDiagonal_nonneg_via_sqrt
    (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ)
    (hpos : ∀ᵐ x ∂μ, ∀ k, 0 ≤ a x k) :
    0 ≤ fieldDiagonal a C hC ha hm := by
  let b : X → Weight := fun x => PolarSupport.sqrtRealWeight (a x)
  have hb : ∀ x, ‖b x‖ ≤ Real.sqrt C := by
    intro x
    apply lp.norm_le_of_forall_le (Real.sqrt_nonneg C)
    intro k
    change ‖(Real.sqrt (a x k).re : ℂ)‖ ≤ Real.sqrt C
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((Complex.re_le_norm _).trans
      ((lp.norm_apply_le_norm (by simp) (a x) k).trans (ha x)))
  have hbm : ∀ k, AEStronglyMeasurable (fun x => b x k) μ := by
    intro k
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      (Real.continuous_sqrt.comp_aestronglyMeasurable
        (Complex.continuous_re.comp_aestronglyMeasurable (hm k)))
  have hbs : ∀ x, ‖star (b x)‖ ≤ Real.sqrt C := by
    simpa only [norm_star] using hb
  have hbsm : ∀ k, AEStronglyMeasurable (fun x => star (b x) k) μ := by
    intro k
    simpa only [lp.coeFn_star, Pi.star_apply] using
      continuous_star.comp_aestronglyMeasurable (hbm k)
  have hfactor : fieldDiagonal a C hC ha hm =
      fieldDiagonal (fun x => star (b x)) (Real.sqrt C)
        (Real.sqrt_nonneg C) hbs hbsm *
      fieldDiagonal b (Real.sqrt C) (Real.sqrt_nonneg C) hb hbm := by
    apply fieldDiagonal_mul_of_coeff_eq
    filter_upwards [hpos] with x hx k
    have heq := congrArg (fun w : Weight => w k)
      (PolarSupport.star_sqrtRealWeight_mul (a x) hx)
    exact heq.symm
  have hstar : fieldDiagonal (fun x => star (b x)) (Real.sqrt C)
      (Real.sqrt_nonneg C) hbs hbsm =
      star (fieldDiagonal b (Real.sqrt C) (Real.sqrt_nonneg C) hb hbm) :=
    fieldDiagonal_star_of_eq (Eventually.of_forall fun _ => rfl)
  rw [hfactor, hstar]
  exact star_mul_self_nonneg _

theorem fieldDiagonal_isPositive_via_sqrt
    (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ)
    (hpos : ∀ᵐ x ∂μ, ∀ k, 0 ≤ a x k) :
    (fieldDiagonal a C hC ha hm).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp
    (fieldDiagonal_nonneg_via_sqrt a C hC ha hm hpos)

end Invariant233.WeightedShift

end

end OAI
