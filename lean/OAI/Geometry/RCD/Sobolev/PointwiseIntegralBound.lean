import OAI.Geometry.RCD.Sobolev.LipschitzL2PointControl

namespace OAI

/-! # Continuous pointwise bounds from finite-set integral tests -/

open Set Filter MeasureTheory Metric
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [SigmaFinite μ] [Measure.IsOpenPosMeasure μ]

omit [BorelSpace X] in
theorem continuous_abs_le_of_setIntegral_bound {v : X → ℝ} (hv : Continuous v)
    (hvi : ∀ S, MeasurableSet S → μ S < ∞ → IntegrableOn v S μ)
    {b : ℝ} (hb : ∀ S, MeasurableSet S → μ S < ∞ → |∫ x in S, v x ∂μ| ≤ b * μ.real S)
    (x : X) : |v x| ≤ b := by
  have hm : 0 ≤ᵐ[μ] fun y => b - v y := by
    apply ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
    · intro S hS hf
      exact (integrableOn_const (C := b) hf.ne).sub (hvi S hS hf)
    · intro S hS hf
      rw [integral_sub (integrableOn_const (C := b) hf.ne) (hvi S hS hf), integral_const,
        smul_eq_mul, measureReal_restrict_apply MeasurableSet.univ, univ_inter]
      have hh := (le_abs_self (∫ y in S, v y ∂μ)).trans (hb S hS hf)
      nlinarith
  have hp : 0 ≤ᵐ[μ] fun y => b + v y := by
    apply ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
    · intro S hS hf
      exact (integrableOn_const (C := b) hf.ne).add (hvi S hS hf)
    · intro S hS hf
      rw [integral_add (integrableOn_const (C := b) hf.ne) (hvi S hS hf), integral_const,
        smul_eq_mul, measureReal_restrict_apply MeasurableSet.univ, univ_inter]
      have hh := (abs_le.mp (hb S hS hf)).1
      nlinarith
  have ha : ∀ᵐ y ∂μ, |v y| ≤ b := by
    filter_upwards [hm, hp] with y hy hz
    change 0 ≤ b - v y at hy
    change 0 ≤ b + v y at hz
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have he : (fun y => min |v y| b) = fun y => |v y| :=
    Measure.eq_of_ae_eq (ha.mono fun _ hy => min_eq_left hy)
      (hv.abs.min continuous_const) hv.abs
  exact min_eq_left_iff.mp (congrFun he x)

end RegularPointCoordinates

end

end OAI
