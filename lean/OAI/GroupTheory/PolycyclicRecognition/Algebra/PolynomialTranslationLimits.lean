import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGroupLaws
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Measure.ContinuousPreimage

namespace OAI

/-! # Small translations in a compact family of polynomial group laws

Normalized brackets can vary with the box. Their compactness and the exact
unit identity still make a vanishing right translation uniformly small on
each fixed coordinate compact set.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter Set MeasureTheory
open scoped Topology symmDiff

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Uniformity in the normalized bracket is essential: the sequence of laws
need not converge. Only the translation vector tends to zero. -/
theorem dynkin_translations_tendstoUniformlyOn
    {c : ℕ} (a : DynkinCoefficients c 2)
    (P : Set (V →L[ℝ] V →L[ℝ] V)) (hP : IsCompact P)
    (hunit : ∀ B ∈ P, ∀ x, dynkinProduct a B x 0 = x)
    {l : Filter ι} (B : ι → V →L[ℝ] V →L[ℝ] V) (hB : ∀ i, B i ∈ P)
    (q : ι → V) (hq : Tendsto q l (𝓝 0))
    (K : Set V) (hK : IsCompact K) :
    TendstoUniformlyOn (fun i x => dynkinProduct a (B i) x (q i)) id l K := by
  let f : V × ((V →L[ℝ] V →L[ℝ] V) × V) → V :=
    fun z => dynkinProduct a z.2.1 z.2.2 z.1
  have hf : Continuous f := by
    exact continuous_dynkinProduct (P := V × ((V →L[ℝ] V →L[ℝ] V) × V)) a
      (fun z => z.2.1) (fun z => z.2.2) (fun z => z.1)
      (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd) continuous_fst
  have hc : IsCompact (Metric.closedBall (0 : V) 1 ×ˢ (P ×ˢ K)) :=
    (isCompact_closedBall _ _).prod (hP.prod hK)
  have hu' : UniformContinuousOn f (Metric.closedBall (0 : V) 1 ×ˢ (P ×ˢ K)) :=
    hc.uniformContinuousOn_of_continuous hf.continuousOn
  have hu := (Metric.uniformContinuousOn_iff (f := f)).mp hu'
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := hu ε hε
  have he := (Metric.tendsto_nhds.mp hq) (min 1 δ) (lt_min zero_lt_one hδ)
  filter_upwards [he] with i hi
  intro x hx
  have hqi : dist (q i) 0 < δ := hi.trans_le (min_le_right _ _)
  have hq1 : q i ∈ Metric.closedBall (0 : V) 1 :=
    hi.le.trans (min_le_left _ _)
  have hzero : (0 : V) ∈ Metric.closedBall (0 : V) 1 := by simp
  have h := hb (q i, (B i, x)) ⟨hq1, hB i, hx⟩
    (0, (B i, x)) ⟨hzero, hB i, hx⟩ (by simpa using hqi)
  simpa only [f, hunit (B i) (hB i) x, id_eq, dist_comm] using h

/-- The coordinate translation converges in the compact-open topology. -/
theorem dynkin_translation_maps_tendsto
    {c : ℕ} (a : DynkinCoefficients c 2)
    (P : Set (V →L[ℝ] V →L[ℝ] V)) (hP : IsCompact P)
    (hunit : ∀ B ∈ P, ∀ x, dynkinProduct a B x 0 = x)
    {l : Filter ι} (B : ι → V →L[ℝ] V →L[ℝ] V) (hB : ∀ i, B i ∈ P)
    (q : ι → V) (hq : Tendsto q l (𝓝 0)) :
    Tendsto (fun i => (⟨fun x => dynkinProduct a (B i) x (q i),
      continuous_dynkinProduct a _ _ _ continuous_const continuous_id continuous_const⟩ : C(V, V)))
      l (𝓝 (ContinuousMap.id V)) := by
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  exact dynkin_translations_tendstoUniformlyOn a P hP hunit B hB q hq K hK

/-- For a normalized Haar measure, small polynomial translations preserve a
fixed finite cell up to a symmetric difference of vanishing measure. -/
theorem measure_dynkin_translation_symmDiff_tendsto_zero
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ]
    {c : ℕ} (a : DynkinCoefficients c 2)
    (P : Set (V →L[ℝ] V →L[ℝ] V)) (hP : IsCompact P)
    (hunit : ∀ B ∈ P, ∀ x, dynkinProduct a B x 0 = x)
    {l : Filter ι} (B : ι → V →L[ℝ] V →L[ℝ] V) (hB : ∀ i, B i ∈ P)
    (q : ι → V) (hq : Tendsto q l (𝓝 0))
    (hpres : ∀ i, MeasurePreserving (fun x => dynkinProduct a (B i) x (q i)) μ μ)
    {S : Set V} (hS : MeasurableSet S) (hfin : μ S ≠ ⊤) :
    Tendsto (fun i => μ (((fun x => dynkinProduct a (B i) x (q i)) ⁻¹' S) ∆ S))
      l (𝓝 0) := by
  let f : ι → C(V, V) := fun i =>
    ⟨fun x => dynkinProduct a (B i) x (q i),
      continuous_dynkinProduct a _ _ _ continuous_const continuous_id continuous_const⟩
  have hf : Tendsto f l (𝓝 (ContinuousMap.id V)) :=
    dynkin_translation_maps_tendsto a P hP hunit B hB q hq
  have hp : ∀ᶠ i in l, MeasurePreserving (f i) μ μ := Eventually.of_forall hpres
  have hi : MeasurePreserving (ContinuousMap.id V) μ μ := MeasurePreserving.id μ
  have ht := tendsto_measure_symmDiff_preimage_nhds_zero
    (μ := μ) (ν := μ) (s := S) hf hp hi hS.nullMeasurableSet hfin
  simpa only [f, ContinuousMap.coe_mk, ContinuousMap.coe_id, preimage_id_eq, id_eq] using ht

end PolycyclicRecognition

end

end OAI
