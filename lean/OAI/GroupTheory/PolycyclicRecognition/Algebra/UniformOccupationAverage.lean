import OAI.GroupTheory.PolycyclicRecognition.Analysis.UniformBoxTranslation

namespace OAI

/-! # Averaging the uniform cell-translation error -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Module Filter
open scoped Manifold Topology

/-- Uniform convergence to zero passes to every probability average.
The norm estimate also covers any nonintegrable early terms. -/
theorem integral_tendsto_zero_of_uniformly_zero
    {ι Z V : Type*} [MeasurableSpace Z] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure Z) [IsProbabilityMeasure μ] {l : Filter ι}
    (f : ι → Z → V) (hf : TendstoUniformly f (fun _ => 0) l) :
    Tendsto (fun i => ∫ z, f i z ∂μ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp hf) (ε / 2) (half_pos hε)] with i hi
  have hb := norm_integral_le_of_norm_le_const (μ := μ) (f := f i)
    (C := ε / 2) (Eventually.of_forall (fun z => by
      simpa only [dist_zero_left] using (hi z).le))
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at hb
  simpa only [dist_zero_right] using hb.trans_lt (half_lt_self hε)

/-- Uniform control is needed only on a set carrying the sampling measure.
This is the form used for a compactly supported chart density. -/
theorem integral_tendsto_zero_of_uniformly_supported_zero
    {ι Z V : Type*} [MeasurableSpace Z] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure Z) [IsProbabilityMeasure μ] {l : Filter ι}
    (K : Set Z) (hK : ∀ᵐ z ∂μ, z ∈ K) (f : ι → Z → V)
    (hf : TendstoUniformly (fun i (z : K) => f i z) (fun _ => 0) l) :
    Tendsto (fun i => ∫ z, f i z ∂μ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp hf) (ε / 2) (half_pos hε)] with i hi
  have hb := norm_integral_le_of_norm_le_const (μ := μ) (f := f i)
    (C := ε / 2) (hK.mono (fun z hz => by
      simpa only [dist_zero_left] using (hi ⟨z, hz⟩).le))
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at hb
  simpa only [dist_zero_right] using hb.trans_lt (half_lt_self hε)

/-- The normalized cell average remains asymptotically invariant after any
independent probability sampling of the chart parameter. -/
theorem averaged_model_cell_error_tendsto_zero
    {E G L ι Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [LieRing L] [LieAlgebra ℝ L]
    [MeasurableSpace Z] (ν : Measure Z) [IsProbabilityMeasure ν]
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {n c : ℕ} (b : ι → Basis (Fin n) ℝ L)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    {C : ℝ} (hbound : ∀ i, ‖basisBracket (b i)‖ ≤ C)
    {l : Filter ι} (q : ι → Z → Fin n → ℝ)
    (hq : TendstoUniformly q (fun _ => 0) l)
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) (hfin : volume S ≠ ⊤)
    (f : ι → Z → (Fin n → ℝ) → ℝ)
    (hf : ∀ i z, AEStronglyMeasurable (f i z) volume)
    {D : ℝ} (hD : 0 ≤ D) (hfbound : ∀ i z x, ‖f i z x‖ ≤ D) :
    Tendsto (fun i => (volume S).toReal⁻¹ * ∫ z,
      ((∫ x in S, f i z (dynkinProduct a (basisBracket (b i)) x (q i z))) -
        ∫ x in S, f i z x) ∂ν) l (𝓝 0) := by
  have hu := model_cell_observable_error_tendstoUniformly haar Exp hExp e hnil
    b a hm hbound q hq hS hfin f hf hD hfbound
  have ht := integral_tendsto_zero_of_uniformly_zero ν _ hu
  simpa only [mul_zero] using tendsto_const_nhds.mul ht

end PolycyclicRecognition

end

end OAI
