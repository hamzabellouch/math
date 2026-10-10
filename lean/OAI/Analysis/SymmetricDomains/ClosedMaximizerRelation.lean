import Mathlib
import OAI.Analysis.SymmetricDomains.WeightedSquaredChartLimit

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Metric Complex
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem analytic_peak_weighted_bound {f : E × F → ℂ}
    {p : FormalMultilinearSeries ℂ (E × F) ℂ}
    (hf : HasFPowerSeriesAt f p 0) (hf0 : f 0 = 0)
    (hlin : ∀ z : E, p 1 (fun _ => (z,0)) = 0)
    {Φ : E × F → G} {L : (E × F) →L[ℝ] G}
    (hΦ : HasFDerivAt Φ L 0) (x : E × F)
    (hpeak : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖Φ (weightedScale t x)-Φ 0‖^2 ≤ -(f (weightedScale t x)).re) :
    ‖L (x.1,0)‖^2 ≤ -(p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,0))).re := by
  have ht := parabolic_taylor_uniformly_compact (hf.restrictScalars (𝕜 := ℝ)) hf0
    hlin (isCompact_singleton (x := x))
  have ht' := (uniform_reindex ht sqrt_tendsto_pos).tendsto_at (mem_singleton x)
  have hh : Tendsto (fun t : ℝ => t⁻¹ • f (weightedScale t x)) (𝓝[>] 0)
      (𝓝 (p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,0)))) := by
    apply ht'.congr'
    filter_upwards [show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin] with t ht
    simp only [parabolicScale,weightedScale,Real.sq_sqrt ht.le]
  have hright : Tendsto (fun t : ℝ => t⁻¹*(-(f (weightedScale t x)).re)) (𝓝[>] 0)
      (𝓝 (-(p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,0))).re)) := by
    simpa only [Function.comp_def,neg_re,smul_re,smul_eq_mul,mul_neg] using
      (Complex.continuous_re.continuousAt.tendsto.comp hh).neg
  apply le_of_tendsto_of_tendsto (weighted_squared_chart_limit hΦ x) hright
  filter_upwards [hpeak,show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin] with t hp ht
  exact mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr ht.le)

end

open Set MeasureTheory Module Filter
open scoped Topology ENNReal

theorem supported_positive_fiber
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure E) (ν : Measure F) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (S : ℕ → Set (E × F)) (hS : ∀ i, MeasurableSet (S i))
    (A : ℕ → E × F → E × F) (hA : ∀ i, DifferentiableOn ℝ (A i) (S i))
    (bad : ℕ → Set E) (hbad : ∀ i, μ (bad i) = 0)
    (T : Set (E × F)) (hT : (μ.prod ν) T ≠ 0)
    (hcover : T ⊆ ⋃ i, A i '' S i) :
    ∃ i x, x ∉ bad i ∧ ν (Prod.mk x ⁻¹' S i) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hzero : ∀ i, (μ.prod ν) (S i) = 0 := by
    intro i
    apply Measure.measure_prod_null_of_ae_null (hS i)
    filter_upwards [show ∀ᵐ x ∂μ, x ∉ bad i from by
      rw [ae_iff]
      have he : {a | ¬a ∉ bad i} = bad i := by ext a; simp
      rw [he]
      exact hbad i] with x hx
    exact hn i x hx
  have himage : ∀ i, (μ.prod ν) (A i '' S i) = 0 := by
    intro i
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (μ.prod ν) (hA i) (hzero i)
  exact hT (measure_mono_null hcover (measure_iUnion_null himage))

theorem affine_image_spans_of_positive_measure
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [AddCommGroup G] [Module ℝ G]
    (ν : Measure F) [ν.IsAddHaarMeasure] {s : Set F} (hs : ν s ≠ 0)
    (A : F →ᵃ[ℝ] G) (hA : Function.Surjective A) :
    Submodule.span ℝ (A '' s) = ⊤ := by
  by_contra hspan
  let W := (Submodule.span ℝ (A '' s)).toAffineSubspace.comap A
  have hW : W ≠ ⊤ := by
    intro h
    apply hspan
    apply top_unique
    intro v _
    obtain ⟨x,rfl⟩ := hA v
    have hx : x ∈ W := by rw [h]; trivial
    exact hx
  apply hs
  apply measure_mono_null (t := (W : Set F))
  · intro x hx
    exact Submodule.subset_span (mem_image_of_mem A hx)
  · exact Measure.addHaar_affineSubspace ν W hW

theorem exists_independent_affine_images_of_positive_measure
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]
    (ν : Measure F) [ν.IsAddHaarMeasure] {s : Set F} (hs : ν s ≠ 0)
    (A : F →ᵃ[ℝ] G) (hA : Function.Surjective A) :
    ∃ v : Fin (finrank ℝ G) → F, (∀ i, v i ∈ s) ∧
      LinearIndependent ℝ (fun i => A (v i)) := by
  classical
  have hspan := affine_image_spans_of_positive_measure ν hs A hA
  let b := Basis.ofSpan (s := A '' s) (show ⊤ ≤ Submodule.span ℝ (A '' s) by rw [hspan])
  let b' := b.reindex (b.indexEquiv (finBasis ℝ G))
  have hb : ∀ i, ∃ v ∈ s, A v = b' i := by
    intro i
    apply Basis.ofSpan_subset (show ⊤ ≤ Submodule.span ℝ (A '' s) by rw [hspan])
    refine ⟨(b.indexEquiv (finBasis ℝ G)).symm i,?_⟩
    change b _ = b.reindex _ i
    simp only [Basis.reindex_apply]
  choose v hv hvb using hb
  refine ⟨v,hv,?_⟩
  have he : (fun i => A (v i)) = b' := funext hvb
  rw [he]
  exact b'.linearIndependent

theorem isClosed_maximizer_relation {X P : Type*} [TopologicalSpace X]
    [TopologicalSpace P] {K : Set X} (hK : IsClosed K)
    {w : P → X → ℝ} (hw : Continuous (Function.uncurry w)) :
    IsClosed {z : X × P | z.1 ∈ K ∧ ∀ q ∈ K, w z.2 q ≤ w z.2 z.1} := by
  have hc : IsClosed {z : X × P | ∀ q ∈ K, w z.2 q ≤ w z.2 z.1} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro q
    apply isClosed_iInter
    intro _hq
    exact isClosed_le (hw.comp (continuous_snd.prodMk continuous_const))
      (hw.comp (continuous_snd.prodMk continuous_fst))
  exact (hK.preimage continuous_fst).inter hc

end Release061

end

end OAI
