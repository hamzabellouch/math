import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.HitValue
import OAI.Probability.CriticalPercolation.GraphGeometry.RestrictVertices
import OAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open Set
open scoped Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def hitEvent (o : V) (A : Set V) : Set (Set E) :=
  {ω | (G.cluster ω o ∩ A).Nonempty}

lemma measurableSet_hitEvent [Countable V] [Countable E] (o : V) (A : Set V) :
    MeasurableSet (G.hitEvent o A) := by
  exact (Measurable.exists fun v => (G.measurable_reachable o v).and measurable_const).setOf

lemma hitEvent_mono_edges (o : V) (A : Set V) {ω ω' : Set E} (h : ω ⊆ ω') :
    ω ∈ G.hitEvent o A → ω' ∈ G.hitEvent o A :=
  fun hω => hω.mono (Set.inter_subset_inter_left A (G.cluster_mono h o))

lemma hitEvent_mono_target (o : V) {A A' : Set V} (h : A ⊆ A') :
    G.hitEvent o A ⊆ G.hitEvent o A' :=
  fun _ hω => hω.mono (Set.inter_subset_inter_right _ h)

lemma expect_hit_eq_real [Fintype E] (q : E → unitInterval) (o : V) (A : Set V) :
    expect (fun e => bitWeight (q e))
      (fun ω => hitValue A (component (G.openGraph ω) o)) =
        (BernoulliProduct.law q).real (G.hitEvent o A) := by
  erw [← integral_law_eq_expect q (fun ω : Set E =>
    hitValue A (component (G.openGraph ω) o))]
  have he : (fun ω : Set E => hitValue A (component (G.openGraph ω) o)) =
      (G.hitEvent o A).indicator (1 : Set E → ℝ) := by
    funext ω
    simp only [hitValue, Set.indicator_apply, Pi.one_apply, hitEvent,
      component, cluster, Set.mem_ofPred_eq]
    rfl
  rw [he, integral_indicator_one (.of_discrete)]

lemma expect_jointHit_eq_real [Fintype E] (q : E → unitInterval) (o : V) (A T : Set V) :
    expect (fun e => bitWeight (q e))
      (fun ω => jointHitValue A T (component (G.openGraph ω) o)) =
        (BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  erw [← integral_law_eq_expect q (fun ω : Set E =>
    jointHitValue A T (component (G.openGraph ω) o))]
  have he : (fun ω : Set E => jointHitValue A T (component (G.openGraph ω) o)) =
      (G.hitEvent o A ∩ G.hitEvent o T).indicator (1 : Set E → ℝ) := by
    funext ω
    simp only [jointHitValue, Set.indicator_apply, Pi.one_apply, hitEvent,
      component, cluster, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rfl
  rw [he, integral_indicator_one (.of_discrete)]

lemma finite_edge_joint_gluing_law [Fintype E] (q : E → unitInterval)
    (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (BernoulliProduct.law q).real (G.hitEvent v T)) :
    (BernoulliProduct.law q).real (G.hitEvent o A) * a ≤
      (BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  rw [← G.expect_hit_eq_real, ← G.expect_jointHit_eq_real]
  apply G.finite_edge_joint_gluing _ (fun e => bitWeight_sum (q e))
    (fun e b => bitWeight_nonneg (q e) b) o A T hA a
  intro v hv
  rw [G.expect_hit_eq_real]
  exact ha v hv

def restrictEdges (s : Set E) : BondGraph V s where
  ends e := G.ends e

lemma restrictEdges_openGraph (s : Set E) (ω : Set E) :
    (G.restrictEdges s).openGraph (Subtype.val ⁻¹' ω) = G.openGraph (s ∩ ω) := by
  unfold openGraph restrictEdges
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Subtype.exists]
  constructor
  · rintro ⟨e, hs, hω, rfl⟩
    exact ⟨e, ⟨hs, hω⟩, rfl⟩
  · rintro ⟨e, ⟨hs, hω⟩, rfl⟩
    exact ⟨e, hs, hω, rfl⟩

lemma restrictEdges_hitEvent (s : Set E) (o : V) (A : Set V) :
    (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹'
        ((G.restrictEdges s).hitEvent o A) =
      {ω | s ∩ ω ∈ G.hitEvent o A} := by
  ext ω
  simp only [Set.mem_preimage, hitEvent, cluster, Set.mem_ofPred_eq,
    G.restrictEdges_openGraph]

lemma finite_subgraph_joint_gluing [Countable V] [Countable E]
    (q : E → unitInterval) (s : Set E) (hs : s.Finite)
    (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (BernoulliProduct.law q).real {ω | s ∩ ω ∈ G.hitEvent v T}) :
    (BernoulliProduct.law q).real {ω | s ∩ ω ∈ G.hitEvent o A} * a ≤
      (BernoulliProduct.law q).real ({ω | s ∩ ω ∈ G.hitEvent o A} ∩
        {ω | s ∩ ω ∈ G.hitEvent o T}) := by
  let : Fintype s := hs.fintype
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  have hr (B : Set (Set s)) (hB : MeasurableSet B) :
      (BernoulliProduct.law (fun e : s => q e)).real B =
        (BernoulliProduct.law q).real ((fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' B) := by
    rw [← law_map_restrict q s]
    simp only [measureReal_def, Measure.map_apply hmeas hB]
  have h := (G.restrictEdges s).finite_edge_joint_gluing_law
    (fun e : s => q e) o A T hA a (by
      intro v hv
      rw [hr _ (.of_discrete), G.restrictEdges_hitEvent]
      exact ha v hv)
  rw [hr _ (.of_discrete), hr _ (.of_discrete), Set.preimage_inter,
    G.restrictEdges_hitEvent, G.restrictEdges_hitEvent] at h
  exact h

lemma finite_subset_exhaustion {X : Type*} {U S : Set X}
    (K : Set.FiniteExhaustion U) (hS : S.Finite) (hSU : S ⊆ U) :
    ∃ n, S ⊆ K n := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨0, Set.empty_subset _⟩
  | @insert x S hx hS ih =>
      obtain ⟨n, hn⟩ := ih (Set.Subset.trans (Set.subset_insert _ _) hSU)
      have hxU := hSU (Set.mem_insert x S)
      rw [← K.iUnion_eq, Set.mem_iUnion] at hxU
      obtain ⟨m, hm⟩ := hxU
      exact ⟨max m n, Set.insert_subset (K.mono (le_max_left _ _) hm)
        (Set.Subset.trans hn (K.mono (le_max_right _ _)))⟩

lemma hitEvent_exhaustion (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o A}) = G.hitEvent o A := by
  ext ω
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact G.hitEvent_mono_edges o A Set.inter_subset_right hn
  · rintro ⟨v, hv, hvA⟩
    obtain ⟨s, hs, hsω, hvs⟩ := G.mem_cluster_finite_witness hv
    obtain ⟨n, hn⟩ := finite_subset_exhaustion K hs (Set.subset_univ s)
    exact Set.mem_iUnion.mpr ⟨n, v, G.cluster_mono
      (Set.subset_inter hn hsω) o hvs, hvA⟩

lemma hitEvent_exhaustion_mono (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    Monotone (fun n => {ω | K n ∩ ω ∈ G.hitEvent o A}) := by
  intro m n h ω hω
  exact G.hitEvent_mono_edges o A (Set.inter_subset_inter_left _ (K.mono h)) hω

lemma tendsto_real_hitEvent_exhaustion [Countable E]
    (q : E → unitInterval) (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    Tendsto (fun n => (BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent o A})
      atTop (𝓝 ((BernoulliProduct.law q).real (G.hitEvent o A))) := by
  have h := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q)
    (G.hitEvent_exhaustion_mono K o A)
  rw [G.hitEvent_exhaustion K o A] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

lemma jointHitEvent_exhaustion (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A T : Set V) :
    (⋃ n, ({ω | K n ∩ ω ∈ G.hitEvent o A} ∩
      {ω | K n ∩ ω ∈ G.hitEvent o T})) = G.hitEvent o A ∩ G.hitEvent o T := by
  calc
    _ = (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o A}) ∩
        (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o T}) :=
      Set.iUnion_inter_of_monotone (G.hitEvent_exhaustion_mono K o A)
        (G.hitEvent_exhaustion_mono K o T)
    _ = _ := by rw [G.hitEvent_exhaustion K o A, G.hitEvent_exhaustion K o T]

lemma tendsto_real_jointHitEvent_exhaustion [Countable E]
    (q : E → unitInterval) (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A T : Set V) :
    Tendsto (fun n => (BernoulliProduct.law q).real
      ({ω | K n ∩ ω ∈ G.hitEvent o A} ∩ {ω | K n ∩ ω ∈ G.hitEvent o T}))
      atTop (𝓝 ((BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T))) := by
  have h := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q)
    ((G.hitEvent_exhaustion_mono K o A).inter (G.hitEvent_exhaustion_mono K o T))
  rw [G.jointHitEvent_exhaustion K o A T] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

lemma finite_sum_abs_sub_bound {X : Type*} [Fintype X] (f g : X → ℝ) (x : X) :
    |f x - g x| ≤ ∑ y, |f y - g y| := by
  exact Finset.single_le_sum (fun y _ => abs_nonneg (f y - g y)) (Finset.mem_univ x)

lemma countable_joint_gluing_finite [Countable V] [Countable E]
    (q : E → unitInterval) (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (BernoulliProduct.law q).real (G.hitEvent v T)) :
    (BernoulliProduct.law q).real (G.hitEvent o A) * a ≤
      (BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  classical
  let : Fintype A := hA.fintype
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  let err : ℕ → ℝ := fun n => ∑ v : A,
    |(BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent v T} -
      (BernoulliProduct.law q).real (G.hitEvent v T)|
  have herr : Tendsto err atTop (𝓝 0) := by
    have h : Tendsto err atTop (𝓝 (∑ _v : A, (0 : ℝ))) := by
      apply tendsto_finsetSum
      intro v _
      simpa using ((G.tendsto_real_hitEvent_exhaustion q K v T).sub_const
        ((BernoulliProduct.law q).real (G.hitEvent v T))).abs
    simpa using h
  have hbound (n : ℕ) :
      (BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent o A} * (a - err n) ≤
      (BernoulliProduct.law q).real ({ω | K n ∩ ω ∈ G.hitEvent o A} ∩
        {ω | K n ∩ ω ∈ G.hitEvent o T}) := by
    refine G.finite_subgraph_joint_gluing q (K n) (K.finite n) o A T hA (a - err n) ?_
    intro v hv
    have hs : |(BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent v T} -
        (BernoulliProduct.law q).real (G.hitEvent v T)| ≤ err n := by
      exact finite_sum_abs_sub_bound
        (fun u : A => (BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent u T})
        (fun u : A => (BernoulliProduct.law q).real (G.hitEvent u T)) ⟨v, hv⟩
    have hneg := (abs_le.mp hs).1
    linarith [ha v hv]
  have hL := (G.tendsto_real_hitEvent_exhaustion q K o A).mul ((tendsto_const_nhds (x := a)).sub herr)
  have hR := G.tendsto_real_jointHitEvent_exhaustion q K o A T
  have h := le_of_tendsto_of_tendsto hL hR (Eventually.of_forall hbound)
  simpa only [sub_zero] using h

lemma hitEvent_iUnion {I : Type*} (o : V) (A : I → Set V) :
    G.hitEvent o (⋃ i, A i) = ⋃ i, G.hitEvent o (A i) := by
  ext ω
  simp only [hitEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Set.nonempty_def,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨v, hv, i, hi⟩
    exact ⟨i, v, hv, hi⟩
  · rintro ⟨i, v, hv, hi⟩
    exact ⟨v, hv, i, hi⟩

theorem countable_joint_gluing [Countable V] [Countable E]
    (q : E → unitInterval) (o : V) (A T : Set V) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (BernoulliProduct.law q).real (G.hitEvent v T)) :
    (BernoulliProduct.law q).real (G.hitEvent o A) * a ≤
      (BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  let K := (Set.to_countable A).finiteExhaustion
  have hKA (n : ℕ) : K n ⊆ A := by
    exact Set.Subset.trans (Set.subset_iUnion K n) (le_of_eq K.iUnion_eq)
  have hmono : Monotone (fun n => G.hitEvent o (K n)) := by
    intro m n h
    exact G.hitEvent_mono_target o (K.mono h)
  have hunion : (⋃ n, G.hitEvent o (K n)) = G.hitEvent o A := by
    rw [← G.hitEvent_iUnion, K.iUnion_eq]
  have hL : Tendsto (fun n => (BernoulliProduct.law q).real (G.hitEvent o (K n)))
      atTop (𝓝 ((BernoulliProduct.law q).real (G.hitEvent o A))) := by
    have h := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q) hmono
    rw [hunion] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  have hR : Tendsto (fun n => (BernoulliProduct.law q).real
      (G.hitEvent o (K n) ∩ G.hitEvent o T))
      atTop (𝓝 ((BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T))) := by
    have h := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q)
      (hmono.inter (monotone_const (c := G.hitEvent o T)))
    rw [← Set.iUnion_inter, hunion] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  exact le_of_tendsto_of_tendsto (hL.mul_const a) hR
    (Eventually.of_forall fun n => G.countable_joint_gluing_finite q o (K n) T
      (K.finite n) a (fun v hv => ha v (hKA n hv)))

theorem joint_gluing [Countable V] [Countable E]
    (p : unitInterval) (o : V) (A T : Set V) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (G.law p).real (G.hitEvent v T)) :
    (G.law p).real (G.hitEvent o A) * a ≤
      (G.law p).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  have he : BernoulliProduct.law (fun _ : E => p) = G.law p := law_const p
  simpa only [he] using G.countable_joint_gluing (fun _ => p) o A T a
    (by simpa only [he] using ha)

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory
open scoped Classical

end
end

end OAI
