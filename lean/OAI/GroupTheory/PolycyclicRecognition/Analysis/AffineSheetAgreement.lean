import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineProfileGluing
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SupportedFlowLipschitz

namespace OAI

/-! # Local agreement identifies affine sheet profiles on the whole domain -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology

/-- Agreement above any nonempty open set identifies both the label and the
offset of affine height profiles. Surjectivity makes the height map open. -/
theorem affine_height_profiles_eq_of_open_agreement
    {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (q : V →L[ℝ] W) (hq : Function.Surjective q)
    (A B : W →L[ℝ] Z) (b c : Z)
    (U O : Set V) (hO : IsOpen O) (hne : O.Nonempty) (hOU : O ⊆ U)
    (f g : V → Z)
    (hf : ∀ z ∈ U, f z = A (q z) + b) (hg : ∀ z ∈ U, g z = B (q z) + c)
    (heq : ∀ z ∈ O, f z = g z) :
    A = B ∧ b = c ∧ ∀ z ∈ U, f z = g z := by
  have hqo : IsOpen (q '' O) := (q.toLinearMap.isOpenMap_of_finiteDimensional hq) O hO
  obtain ⟨hAB, hbc⟩ := affine_parameters_eq_on_open hqo (hne.image q) A B b c (by
    rintro w ⟨z, hz, rfl⟩
    rw [← hf z (hOU hz), ← hg z (hOU hz)]
    exact heq z hz)
  refine ⟨hAB, hbc, ?_⟩
  intro z hz
  rw [hf z hz, hg z hz, hAB, hbc]

/-- A continuous image of a supported sample is supported by its image law. -/
theorem mem_support_map_of_continuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (f : X → Y) (hf : Continuous f)
    {x : X} (hx : x ∈ (μ : Measure X).support) :
    f x ∈ (ProbabilityMeasure.map μ f : Measure Y).support := by
  apply (Measure.mem_support_iff_forall (f x)).mpr
  intro U hU
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  apply lt_of_lt_of_le _ (measure_mono hVU)
  change 0 < Measure.map f (μ : Measure X) V
  rw [Measure.map_apply hf.measurable hV.measurableSet]
  exact (Measure.mem_support_iff_forall x).mp hx _
    (hf.continuousAt.preimage_mem_nhds (hV.mem_nhds hxV))

/-- Projection of a weak limit of sampled pairs is the weak limit of the
projected samples, with no change of sampling law. -/
theorem sampled_projection_tendsto
    {A X Y : Type*} [MeasurableSpace A]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : ℕ → ProbabilityMeasure A) (p : ℕ → A → X) (hp : ∀ n, Measurable (p n))
    (ν : ProbabilityMeasure X)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (μ n) (p n)) atTop (𝓝 ν))
    (f : X → Y) (hf : Continuous f) :
    Tendsto (fun n => ProbabilityMeasure.map (μ n) (f ∘ p n)) atTop
      (𝓝 (ProbabilityMeasure.map ν f)) := by
  have ht := (ProbabilityMeasure.continuous_map hf).tendsto ν |>.comp hν
  apply ht.congr'
  filter_upwards [] with n
  apply Subtype.ext
  exact Measure.map_map hf.measurable (hp n)

/-- A uniform vanishing discrepancy for sampled profile pairs is inherited
by every pair in the support of a weak limit. -/
theorem supported_profile_pair_eq_of_ae_discrepancy
    {V W A : Type*} [TopologicalSpace V] [LocallyCompactSpace V]
    [PseudoMetricSpace W] [MeasurableSpace A]
    (S : Set C(V, W)) [MeasurableSpace (S × S)] [BorelSpace (S × S)]
    [HasOuterApproxClosed (S × S)]
    (samples : ℕ → ProbabilityMeasure A) (pair : ℕ → A → S × S)
    (hp : ∀ n, Measurable (pair n)) (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (pair n)) atTop (𝓝 ν))
    (z : V) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ᵐ a ∂(samples n : Measure A),
      dist ((pair n a).1.val z) ((pair n a).2.val z) ≤ ε n)
    {f : S × S} (hf : f ∈ (ν : Measure (S × S)).support) :
    dist (f.1.val z) (f.2.val z) = 0 := by
  let obs : S × S → ℝ := fun f => dist (f.1.val z) (f.2.val z)
  have ho : Continuous obs :=
    ((continuous_eval_const z).comp (continuous_subtype_val.comp continuous_fst)).dist
      ((continuous_eval_const z).comp (continuous_subtype_val.comp continuous_snd))
  have h := le_on_support_of_ae_sample_bound samples pair hp ν hν
    (fun _ => obs) obs ho (by
      apply Metric.tendstoUniformly_iff.mpr
      intro ε hε
      exact Eventually.of_forall (fun _ _ => by simpa only [dist_self] using hε)) ε hε 0
    (by simpa only [zero_add] using hbound) hf
  exact le_antisymm h dist_nonneg

/-- Pointwise sample bounds imply the almost-everywhere version. -/
theorem supported_profile_pair_eq_of_uniform_discrepancy
    {V W A : Type*} [TopologicalSpace V] [LocallyCompactSpace V]
    [PseudoMetricSpace W] [MeasurableSpace A]
    (S : Set C(V, W)) [MeasurableSpace (S × S)] [BorelSpace (S × S)]
    [HasOuterApproxClosed (S × S)]
    (samples : ℕ → ProbabilityMeasure A) (pair : ℕ → A → S × S)
    (hp : ∀ n, Measurable (pair n)) (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (pair n)) atTop (𝓝 ν))
    (z : V) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ a,
      dist ((pair n a).1.val z) ((pair n a).2.val z) ≤ ε n)
    {f : S × S} (hf : f ∈ (ν : Measure (S × S)).support) :
    dist (f.1.val z) (f.2.val z) = 0 := by
  exact supported_profile_pair_eq_of_ae_discrepancy S samples pair hp ν hν z ε hε
    (hbound.mono fun _ hn => Filter.Eventually.of_forall hn) hf

end PolycyclicRecognition

end

end OAI
