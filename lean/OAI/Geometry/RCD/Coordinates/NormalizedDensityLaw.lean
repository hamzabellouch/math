import OAI.Geometry.RCD.Coordinates.NormalizedProbabilityLaw
import OAI.Analysis.RCDHeat.ProbabilityCutoff

namespace OAI

/-! # Exact probability laws from nonnegative densities

The normalizing integral is retained explicitly, including for measurable
pullbacks to the original metric space.
-/

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

def normalizedDensityLaw (μ : Measure X) {f : X → ℝ}
    (hi : Integrable f μ) (hn : ∀ x, 0≤f x) (hp : 0<∫ x, f x ∂μ) : ProbabilityMeasure X := by
  refine ⟨μ.withDensity (fun x => ENNReal.ofReal ((∫ y, f y ∂μ)⁻¹*f x)),?_⟩
  apply realDensity_probability μ (hi.const_mul _)
  · exact Eventually.of_forall fun x => mul_nonneg (inv_nonneg.mpr hp.le) (hn x)
  · rw [integral_const_mul,inv_mul_cancel₀ hp.ne']

theorem normalizedDensityLaw_integral (μ : Measure X) {f : X → ℝ} (hf : Measurable f)
    (hi : Integrable f μ) (hn : ∀ x, 0≤f x) (hp : 0<∫ x, f x ∂μ) (g : X → ℝ) :
    (∫ x, g x ∂(normalizedDensityLaw μ hi hn hp : Measure X))=
      (∫ x, f x ∂μ)⁻¹*(∫ x, f x*g x ∂μ) := by
  change (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal ((∫ y, f y ∂μ)⁻¹*f x)))=_
  rw [integral_withDensity_eq_integral_toReal_smul (hf.const_mul _).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hp.le) (hn _)),
    smul_eq_mul,mul_assoc]
  exact integral_const_mul _ _

theorem normalizedDensityLaw_le (μ : Measure X) {f : X → ℝ}
    (hi : Integrable f μ) (hn : ∀ x, 0≤f x) (hp : 0<∫ x, f x ∂μ)
    {B : ℝ} (hB : ∀ x, f x≤B) :
    (normalizedDensityLaw μ hi hn hp : Measure X)≤
      ENNReal.ofReal ((∫ x, f x ∂μ)⁻¹*B) • μ := by
  change μ.withDensity _≤_
  rw [← withDensity_const]
  apply withDensity_mono
  exact Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (hB x) (inv_nonneg.mpr hp.le))

theorem normalizedDensityLaw_tendsto {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μs : ℕ → ProbabilityMeasure Y) (μ : ProbabilityMeasure Y)
    (hμ : Tendsto μs atTop (𝓝 μ)) (f : Y →ᵇ ℝ) (hn : ∀ y, 0≤f y)
    (hpos : 0<∫ y, f y ∂(μ : Measure Y))
    (hposs : ∀ k, 0<∫ y, f y ∂(μs k : Measure Y)) :
    Tendsto (fun k => normalizedDensityLaw (μs k : Measure Y)
      (f.integrable _) hn (hposs k)) atTop
      (𝓝 (normalizedDensityLaw (μ : Measure Y) (f.integrable _) hn hpos)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  simp_rw [normalizedDensityLaw_integral _ f.continuous.measurable]
  have ha := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f
  have hb := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ (f*g)
  exact ha.inv₀ hpos.ne' |>.mul hb

end RegularPointCoordinates

end

end OAI
