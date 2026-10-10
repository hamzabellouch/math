import OAI.GroupTheory.PolycyclicRecognition.Analysis.OccupationSampling
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DensityOccupationError
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniformOccupationAverage

namespace OAI

/-! # Passing coordinate translation estimates to sampled probabilities -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter
open scoped Topology

/-- Translation in the density-sampled factor changes the law by a
vanishing amount. The other independent factor can vary through the
observable and requires no uniformity in its sample points. -/
theorem density_product_occupation_error_tendsto_zero
    {A D X G ι : Type*} [MeasurableSpace A]
    [TopologicalSpace D] [MeasurableSpace D] [BorelSpace D]
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [SMul G X] [ContinuousConstSMul G X]
    (μ : ProbabilityMeasure A) (m : Measure D) [SFinite m]
    (ρ : D → ℝ) (hc : Continuous ρ) (hi : Integrable ρ m)
    (hp : ∀ z, 0 ≤ ρ z) (hmass : ∫ z, ρ z ∂m = 1)
    {l : Filter ι} [l.IsCountablyGenerated]
    (T : ι → D ≃ᵐ D) (hT : ∀ i, MeasurePreserving (T i) m m)
    (hlim : ∀ z, Tendsto (fun i => (T i).symm z) l (𝓝 z))
    (p : ι → A × D → X) (hmeas : ∀ i, Measurable (p i))
    (g : G) (hmove : ∀ i a z, g • p i (a, z) = p i (a, T i z))
    (f : C(X, ℝ)) :
    Tendsto (fun i =>
      (∫ x, f (g • x) ∂(productOccupationLaw μ
        (densityProbabilityMeasure m ρ hi hp hmass) (p i) : Measure X)) -
      ∫ x, f x ∂(productOccupationLaw μ
        (densityProbabilityMeasure m ρ hi hp hmass) (p i) : Measure X)) l (𝓝 0) := by
  let F : ι → D → ℝ := fun i z => ∫ a, f (p i (a, z)) ∂(μ : Measure A)
  have hF (i : ι) : AEStronglyMeasurable (F i) m :=
    ((f.continuous.measurable.comp (hmeas i)).stronglyMeasurable.integral_prod_left').aestronglyMeasurable
  have hbound (i : ι) (z : D) : ‖F i z‖ ≤ ‖f‖ := by
    have hh := norm_integral_le_of_norm_le_const (μ := (μ : Measure A))
      (f := fun a => f (p i (a, z))) (C := ‖f‖)
      (Eventually.of_forall (fun a => f.norm_coe_le_norm _))
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using hh
  have ht := density_occupation_error_tendsto_zero m ρ hc hi hp T hT hlim
    F hF (norm_nonneg f) hbound
  apply ht.congr
  intro i
  let fg : C(X, ℝ) := ⟨fun x => f (g • x),
    f.continuous.comp (continuous_const_smul g)⟩
  have hfg := integral_productOccupationLaw_symm μ
    (densityProbabilityMeasure m ρ hi hp hmass) (p i) (hmeas i) fg
  have hff := integral_productOccupationLaw_symm μ
    (densityProbabilityMeasure m ρ hi hp hmass) (p i) (hmeas i) f
  change _ = _ - _
  rw [show (fun x => f (g • x)) = (fg : X → ℝ) from rfl, hfg, hff]
  simp_rw [integral_densityProbabilityMeasure, fg, ContinuousMap.coe_mk, hmove]
  rfl

/-- A uniform first-factor error remains small after independent sampling
of the other coordinate, and is exactly the translated-law error. -/
theorem first_factor_product_occupation_error_tendsto_zero
    {A D X G ι : Type*} [MeasurableSpace A] [MeasurableSpace D]
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [SMul G X] [ContinuousConstSMul G X]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure D)
    {l : Filter ι} (p : ι → A × D → X) (hmeas : ∀ i, Measurable (p i))
    (U : ι → D → A → A) (g : G)
    (hmove : ∀ i a d, g • p i (a, d) = p i (U i d a, d))
    (f : C(X, ℝ))
    (herror : TendstoUniformly (fun i d =>
      (∫ a, f (p i (U i d a, d)) ∂(μ : Measure A)) -
      ∫ a, f (p i (a, d)) ∂(μ : Measure A)) (fun _ => 0) l) :
    Tendsto (fun i =>
      (∫ x, f (g • x) ∂(productOccupationLaw μ ν (p i) : Measure X)) -
      ∫ x, f x ∂(productOccupationLaw μ ν (p i) : Measure X)) l (𝓝 0) := by
  have ht := integral_tendsto_zero_of_uniformly_zero (ν : Measure D) _ herror
  apply ht.congr
  intro i
  let fg : C(X, ℝ) := ⟨fun x => f (g • x),
    f.continuous.comp (continuous_const_smul g)⟩
  have hfg := integral_productOccupationLaw_symm μ ν (p i) (hmeas i) fg
  have hff := integral_productOccupationLaw_symm μ ν (p i) (hmeas i) f
  have hfi (q : C(X, ℝ)) : Integrable (fun z : A × D => q (p i z))
      ((μ : Measure A).prod (ν : Measure D)) :=
    Integrable.of_bound (q.continuous.measurable.comp (hmeas i)).aestronglyMeasurable
      ‖q‖ (Eventually.of_forall (fun z => q.norm_coe_le_norm _))
  change _ = _ - _
  rw [show (fun x => f (g • x)) = (fg : X → ℝ) from rfl, hfg, hff,
    ← integral_sub (hfi fg).integral_prod_right (hfi f).integral_prod_right]
  apply integral_congr_ae
  exact Eventually.of_forall (fun d => by simp only [fg, ContinuousMap.coe_mk, hmove])

end PolycyclicRecognition

end

end OAI
