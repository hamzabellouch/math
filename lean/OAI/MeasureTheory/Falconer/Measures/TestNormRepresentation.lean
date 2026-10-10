import OAI.MeasureTheory.Falconer.Radial.RadialTestNorm
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceTestNorm_test_bound (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {q : ℝ} (hN : sourceTestNorm q γ ≠ ∞)
    (F : BoundedContinuousFunction UnitCircle ℝ) :
    ‖∫ ω, F ω ∂γ‖ ≤ (sourceTestNorm q γ).toReal *
      (eLpNorm F (ENNReal.ofReal q) sourceArcLength).toReal := by
  have hf : MemLp F (ENNReal.ofReal q) sourceArcLength :=
    (memLp_top_of_bound F.continuous.aestronglyMeasurable ‖F‖
      (Eventually.of_forall F.norm_coe_le_norm)).mono_exponent le_top
  have haux (a : ℝ) (ha : (eLpNorm F (ENNReal.ofReal q) sourceArcLength).toReal < a) :
      ‖∫ ω, F ω ∂γ‖ ≤ (sourceTestNorm q γ).toReal * a := by
    have ha0 : 0 < a := lt_of_le_of_lt ENNReal.toReal_nonneg ha
    let G : BoundedContinuousFunction UnitCircle ℝ := a⁻¹ • F
    have hG : eLpNorm G (ENNReal.ofReal q) sourceArcLength ≤ 1 := by
      change eLpNorm (a⁻¹ • (F : UnitCircle → ℝ)) _ _ ≤ _
      rw [eLpNorm_const_smul]
      have hn : eLpNorm F (ENNReal.ofReal q) sourceArcLength ≤ ENNReal.ofReal a :=
        (ENNReal.le_ofReal_iff_toReal_le hf.eLpNorm_ne_top ha0.le).mpr ha.le
      calc
        ‖a⁻¹‖ₑ * eLpNorm F (ENNReal.ofReal q) sourceArcLength ≤
            ENNReal.ofReal a⁻¹ * ENNReal.ofReal a := by
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha0)]
          exact mul_le_mul_right hn _
        _ = 1 := by rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ha0.le), inv_mul_cancel₀ ha0.ne', ENNReal.ofReal_one]
    have hb : ENNReal.ofReal ‖∫ ω, G ω ∂γ‖ ≤ sourceTestNorm q γ :=
      le_iSup_of_le G (le_iSup_of_le hG le_rfl)
    have hb' := (ENNReal.ofReal_le_iff_le_toReal hN).mp hb
    change ‖∫ ω, a⁻¹ • F ω ∂γ‖ ≤ _ at hb'
    rw [integral_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha0)] at hb'
    calc
      ‖∫ ω, F ω ∂γ‖ = a * (a⁻¹ * ‖∫ ω, F ω ∂γ‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul]
      _ ≤ a * (sourceTestNorm q γ).toReal := mul_le_mul_of_nonneg_left hb' ha0.le
      _ = _ := mul_comm _ _
  apply ge_of_tendsto (f := fun a : ℝ => (sourceTestNorm q γ).toReal * a)
    ((continuous_const.mul continuous_id).continuousAt.tendsto.mono_left
      (show 𝓝[>] (eLpNorm F (ENNReal.ofReal q) sourceArcLength).toReal ≤
        𝓝 (eLpNorm F (ENNReal.ofReal q) sourceArcLength).toReal from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact haux a ha

end PlanarFalconer

end OAI
