import OAI.MeasureTheory.Falconer.Measures.TestNormRepresentation
import OAI.MeasureTheory.Falconer.Measures.FiniteLpIntegral

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceTestNorm_measurable_test_bound (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {q : ℝ} (hq : 1 ≤ q) (hN : sourceTestNorm q γ ≠ ∞)
    (f : UnitCircle → ℝ) (hf : MemLp f (ENNReal.ofReal q) (γ + sourceArcLength)) :
    ‖∫ ω, f ω ∂γ‖ ≤ (sourceTestNorm q γ).toReal *
      (eLpNorm f (ENNReal.ofReal q) sourceArcLength).toReal := by
  let μ := γ + sourceArcLength
  let Q := ENNReal.ofReal q
  have hQ : 1 ≤ Q := by simpa [Q] using ENNReal.ofReal_le_ofReal hq
  let : Fact (1 ≤ Q) := ⟨hQ⟩
  have hγ : γ ≤ μ := le_add_of_nonneg_right bot_le
  have hν : sourceArcLength ≤ μ := le_add_of_nonneg_left bot_le
  have hν' : sourceArcLength ≤ (1 : ℝ≥0∞) • μ := by simpa using hν
  let R : Lp ℝ Q μ →L[ℝ] Lp ℝ Q sourceArcLength :=
    Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top hν'
  have hR (g : Lp ℝ Q μ) : R g =ᵐ[sourceArcLength] g :=
    Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top hν' g
  have hd := BoundedContinuousFunction.toLp_denseRange ℝ μ ℝ (show Q ≠ ∞ from ENNReal.ofReal_ne_top)
  have hclosed : IsClosed {g : Lp ℝ Q μ | ‖∫ ω, g ω ∂γ‖ ≤
      (sourceTestNorm q γ).toReal * ‖R g‖} :=
    isClosed_le (continuous_integral_Lp_of_le γ μ hγ hQ).norm
      (continuous_const.mul R.continuous.norm)
  have hall (g : Lp ℝ Q μ) : ‖∫ ω, g ω ∂γ‖ ≤ (sourceTestNorm q γ).toReal * ‖R g‖ := by
    apply (hclosed.closure_subset_iff (s := Set.range (BoundedContinuousFunction.toLp Q μ ℝ))).mpr ?_ (hd g)
    rintro _ ⟨F, rfl⟩
    have hF := BoundedContinuousFunction.coeFn_toLp Q μ ℝ F
    have hi := integral_congr_ae (hγ.absolutelyContinuous.ae_eq hF)
    have hn : ‖R (BoundedContinuousFunction.toLp Q μ ℝ F)‖ =
        (eLpNorm F Q sourceArcLength).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae ((hR _).trans (hν.absolutelyContinuous.ae_eq hF))]
    change ‖∫ ω, (BoundedContinuousFunction.toLp Q μ ℝ F) ω ∂γ‖ ≤ _
    rw [hi, hn]
    exact sourceTestNorm_test_bound γ hN F
  have hg := hall (hf.toLp f)
  have he := hf.coeFn_toLp
  rw [integral_congr_ae (hγ.absolutelyContinuous.ae_eq he)] at hg
  have hn : ‖R (hf.toLp f)‖ = (eLpNorm f Q sourceArcLength).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae ((hR _).trans (hν.absolutelyContinuous.ae_eq he))]
  rwa [hn] at hg

theorem sourceTestNorm_absolutelyContinuous (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {q : ℝ} (hq : 1 ≤ q) (hN : sourceTestNorm q γ ≠ ∞) : γ ≪ sourceArcLength := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hνs
  let f : UnitCircle → ℝ := s.indicator (fun _ => 1)
  have hf : MemLp f (ENNReal.ofReal q) (γ + sourceArcLength) :=
    memLp_indicator_const _ hs _ (Or.inr (measure_ne_top _ _))
  have hb := sourceTestNorm_measurable_test_bound γ hq hN f hf
  have he : f =ᵐ[sourceArcLength] 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hνs] with x hx
    exact Set.indicator_of_notMem hx _
  rw [eLpNorm_congr_ae he, eLpNorm_zero, ENNReal.toReal_zero, mul_zero] at hb
  have hi : (∫ x, f x ∂γ) = (γ s).toReal := by
    simp [f, integral_indicator hs, measureReal_def]
  rw [hi, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hb
  exact ((ENNReal.toReal_eq_zero_iff _).mp (le_antisymm hb ENNReal.toReal_nonneg)).resolve_right
    (measure_ne_top γ s)

end PlanarFalconer

end OAI
