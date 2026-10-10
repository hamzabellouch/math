import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

namespace OAI

/-! # Concentration near a finite family of affine profiles -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal

/-- Restrictions of the finitely many linear profiles, with arbitrary offsets. -/
def affineProfileClass {Z W L : Type*} [TopologicalSpace Z]
    [TopologicalSpace W] [Add W] (A : L → C(Z, W)) : Set C(Z, W) :=
  {f | ∃ a b, ∀ z, f z = A a z + b}

theorem affineProfileClass_nonempty {Z W L : Type*} [TopologicalSpace Z]
    [TopologicalSpace W] [AddGroup W] [Nonempty L] (A : L → C(Z, W)) :
    (affineProfileClass A).Nonempty := by
  obtain ⟨a⟩ := ‹Nonempty L›
  exact ⟨A a, a, 0, fun _ => (add_zero _).symm⟩

/-- One evaluation recovers the offset. This makes the affine class closed
without requiring an a priori bound on its offsets. -/
theorem isClosed_affineProfileClass {Z W L : Type*} [TopologicalSpace Z]
    [TopologicalSpace W] [AddCommGroup W] [IsTopologicalAddGroup W] [T2Space W]
    [Finite L] (A : L → C(Z, W)) (z₀ : Z) :
    IsClosed (affineProfileClass A) := by
  have heq : affineProfileClass A =
      ⋃ a, {f : C(Z, W) | ∀ z, f z = A a z + (f z₀ - A a z₀)} := by
    ext f
    simp only [affineProfileClass, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨a, b, hf⟩
      refine ⟨a, fun z => ?_⟩
      rw [hf z, hf z₀]
      simp
    · rintro ⟨a, hf⟩
      exact ⟨a, _, hf⟩
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro a
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro z
  exact isClosed_eq (continuous_eval_const z)
    (continuous_const.add ((continuous_eval_const z₀).sub continuous_const))

/-- A closed event disjoint from the support of the limit has probability
converging to zero. -/
theorem measure_closed_tendsto_zero_of_support
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [HasOuterApproxClosed S] [HereditarilyLindelofSpace S]
    {μn : ℕ → ProbabilityMeasure S} {μ : ProbabilityMeasure S}
    (hμ : Tendsto μn atTop (𝓝 μ)) {B : Set S} (hB : IsClosed B)
    (hs : ∀ f ∈ (μ : Measure S).support, f ∉ B) :
    Tendsto (fun n => (μn n : Measure S) B) atTop (𝓝 0) := by
  have hz : (μ : Measure S) B = 0 := by
    apply measure_mono_null _ (μ : Measure S).measure_compl_support
    intro f hf
    exact fun hfs => hs f hfs hf
  apply tendsto_of_le_liminf_of_limsup_le zero_le
  simpa only [hz] using ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hB

/-- Compactness turns a statement about every supported sequential limit
into concentration for the original sequence. -/
theorem measure_closed_tendsto_zero_of_all_supported_limits
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [MetrizableSpace S]
    [MeasurableSpace S] [BorelSpace S] (μn : ℕ → ProbabilityMeasure S)
    {B : Set S} (hB : IsClosed B)
    (hs : ∀ (ι : ℕ → ℕ), StrictMono ι → ∀ μ : ProbabilityMeasure S,
      Tendsto (μn ∘ ι) atTop (𝓝 μ) → ∀ f ∈ (μ : Measure S).support, f ∉ B) :
    Tendsto (fun n => (μn n : Measure S) B) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨u, hu, hnu⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨μ, v, hv, hμ⟩ := CompactSpace.tendsto_subseq (μn ∘ ns ∘ u)
  refine ⟨u ∘ v, ?_⟩
  exact measure_closed_tendsto_zero_of_support hμ hB
    (hs (ns ∘ u ∘ v) (hnu.comp hv) μ hμ)

/-- On a compact profile space, affine support of every weak limit gives
vanishing probability of a fixed positive distance from the affine class. -/
theorem affine_distance_concentration
    {V W L : Type*} [TopologicalSpace V] [LocallyCompactSpace V]
    [NormedAddCommGroup W] [Nonempty L]
    (S : Set C(V, W)) [CompactSpace S] [MetrizableSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (μn : ℕ → ProbabilityMeasure S) (Z : Set V) [CompactSpace Z]
    (A : L → C(Z, W))
    (hs : ∀ (ι : ℕ → ℕ), StrictMono ι → ∀ μ : ProbabilityMeasure S,
      Tendsto (μn ∘ ι) atTop (𝓝 μ) → ∀ f ∈ (μ : Measure S).support,
        f.val.restrict Z ∈ affineProfileClass A)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => (μn n : Measure S)
      {f | η ≤ infDist (f.val.restrict Z) (affineProfileClass A)}) atTop (𝓝 0) := by
  have hd : Continuous (fun f : S => infDist (f.val.restrict Z) (affineProfileClass A)) :=
    (continuous_infDist_pt _).comp
      ((ContinuousMap.continuous_restrict Z).comp continuous_subtype_val)
  apply measure_closed_tendsto_zero_of_all_supported_limits μn
    (isClosed_le continuous_const hd)
  intro ι hι μ hμ f hf
  change ¬η ≤ infDist (f.val.restrict Z) (affineProfileClass A)
  rw [infDist_zero_of_mem (hs ι hι μ hμ f hf)]
  exact not_le_of_gt hη

end PolycyclicRecognition

end

end OAI
