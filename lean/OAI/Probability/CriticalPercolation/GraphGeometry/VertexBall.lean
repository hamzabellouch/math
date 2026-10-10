import Mathlib
import OAI.Probability.CriticalPercolation.Model

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem openGraph_mono {ω ω' : Set E} (h : ω ⊆ ω') :
    G.openGraph ω ≤ G.openGraph ω' :=
  SimpleGraph.fromEdgeSet_mono (Set.image_mono h)

theorem cluster_mono {ω ω' : Set E} (h : ω ⊆ ω') (v : V) :
    G.cluster ω v ⊆ G.cluster ω' v :=
  fun _ hw => hw.mono (G.openGraph_mono h)

theorem percolates_mono {ω ω' : Set E} (h : ω ⊆ ω')
    (hω : ω ∈ G.percolates) : ω' ∈ G.percolates := by
  obtain ⟨v, hv⟩ := hω
  exact ⟨v, hv.mono (G.cluster_mono h v)⟩

theorem finite_neighbors (hlocal : G.LocallyFinite) (v : V) :
    (G.fullGraph.neighborSet v).Finite := by
  classical
  have hf : (⋃ e ∈ {e : E | v ∈ G.ends e}, (↑(G.ends e).toFinset : Set V)).Finite :=
    (hlocal v).biUnion fun e _ => (G.ends e).toFinset.finite_toSet
  apply hf.subset
  intro w hw
  obtain ⟨⟨e, _, he⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hw
  apply Set.mem_iUnion₂.mpr
  refine ⟨e, ?_, ?_⟩ <;> simp [he]

def vertexBall (G : BondGraph V E) (o : V) : ℕ → Set V
  | 0 => {o}
  | n + 1 => G.vertexBall o n ∪ ⋃ v ∈ G.vertexBall o n, G.fullGraph.neighborSet v

lemma vertexBall_finite (hlocal : G.LocallyFinite) (o : V) (n : ℕ) :
    (G.vertexBall o n).Finite := by
  induction n with
  | zero => exact Set.finite_singleton o
  | succ n ih => exact ih.union (ih.biUnion fun v _ => G.finite_neighbors hlocal v)

lemma reachable_mem_vertexBall {o v : V} (h : G.fullGraph.Reachable o v) :
    ∃ n, v ∈ G.vertexBall o n := by
  have hr := (G.fullGraph.reachable_iff_reflTransGen o v).mp h
  clear h
  induction hr with
  | refl => exact ⟨0, rfl⟩
  | @tail u w hr huv ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, Or.inr (Set.mem_iUnion₂.mpr ⟨u, hn, huv⟩)⟩

theorem countable_vertices (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) : Countable V := by
  obtain ⟨o⟩ := hconnected.nonempty
  have hc : (⋃ n : ℕ, G.vertexBall o n).Countable :=
    Set.countable_iUnion fun n => (G.vertexBall_finite hlocal o n).countable
  have heq : (⋃ n : ℕ, G.vertexBall o n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨n, hn⟩ := G.reachable_mem_vertexBall (hconnected o v)
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc

theorem countable_bonds (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) : Countable E := by
  let := G.countable_vertices hconnected hlocal
  have hc : (⋃ v : V, {e : E | v ∈ G.ends e}).Countable :=
    Set.countable_iUnion fun v => (hlocal v).countable
  have heq : (⋃ v : V, {e : E | v ∈ G.ends e}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro e
    exact Set.mem_iUnion.mpr ⟨(G.ends e).out.1, Sym2.out_fst_mem _⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc

def lengthReach (H : SimpleGraph V) : ℕ → V → V → Prop
  | 0, v, w => v = w
  | n + 1, v, w => ∃ u, lengthReach H n v u ∧ H.Adj u w

lemma reachable_iff_exists_lengthReach (H : SimpleGraph V) (v w : V) :
    H.Reachable v w ↔ ∃ n, lengthReach H n v w := by
  rw [H.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail u w h huw ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, u, hn, huw⟩
  · rintro ⟨n, hn⟩
    induction n generalizing w with
    | zero => exact hn ▸ Relation.ReflTransGen.refl
    | succ n ih =>
        obtain ⟨u, hu, huw⟩ := hn
        exact (ih u hu).tail huw

lemma measurable_openGraph_adj [Countable E] (v w : V) :
    Measurable (fun ω : Set E => (G.openGraph ω).Adj v w) := by
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  exact (Measurable.exists fun e =>
    (measurable_set_mem e).and measurable_const).and measurable_const

lemma measurable_lengthReach [Countable V] [Countable E] (n : ℕ) (v w : V) :
    Measurable (fun ω : Set E => lengthReach (G.openGraph ω) n v w) := by
  induction n generalizing w with
  | zero => exact measurable_const
  | succ n ih =>
      exact Measurable.exists fun u => (ih u).and (G.measurable_openGraph_adj u w)

lemma measurable_reachable [Countable V] [Countable E] (v w : V) :
    Measurable (fun ω : Set E => (G.openGraph ω).Reachable v w) := by
  simp_rw [reachable_iff_exists_lengthReach]
  exact Measurable.exists fun n => G.measurable_lengthReach n v w

lemma measurable_cluster [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => G.cluster ω v) := by
  exact Measurable.of_eval fun vertex => G.measurable_reachable v vertex

lemma measurable_infinite_cluster [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => (G.cluster ω v).Infinite) := by
  simp_rw [← Set.encard_eq_top_iff]
  exact (measurable_encard.comp (G.measurable_cluster v)).eq_const ⊤

theorem measurableSet_percolates [Countable V] [Countable E] :
    MeasurableSet G.percolates := by
  exact (Measurable.exists fun v => G.measurable_infinite_cluster v).setOf

theorem percolates_null_iff [Countable V] (μ : Measure (Set E)) :
    μ G.percolates = 0 ↔ ∀ v, μ {ω | (G.cluster ω v).Infinite} = 0 := by
  have heq : G.percolates = ⋃ v, {ω | (G.cluster ω v).Infinite} := by
    ext ω
    simp [percolates]
  rw [heq, measure_iUnion_null_iff]

@[simp] lemma openGraph_empty : G.openGraph ∅ = ⊥ := by
  simp [openGraph]

@[simp] lemma cluster_empty (v : V) : G.cluster ∅ v = {v} := by
  ext w
  simp [cluster, SimpleGraph.reachable_bot, eq_comm]

@[simp] lemma empty_not_percolates : ∅ ∉ G.percolates := by
  simp [percolates]

lemma law_zero_percolates [Countable V] [Countable E] : G.law 0 G.percolates = 0 := by
  rw [law, ProbabilityTheory.setBernoulli_zero,
    Measure.dirac_apply' _ G.measurableSet_percolates]
  simp

lemma cluster_univ_of_connected (hconnected : G.fullGraph.Connected) (v : V) :
    G.cluster Set.univ v = Set.univ :=
  Set.eq_univ_of_forall fun w => hconnected v w

lemma law_one_percolates [Infinite V] (hconnected : G.fullGraph.Connected) :
    G.law 1 G.percolates = 1 := by
  rw [law, ProbabilityTheory.setBernoulli_one]
  apply Measure.dirac_apply_of_mem
  obtain ⟨v⟩ := hconnected.nonempty
  refine ⟨v, ?_⟩
  rw [G.cluster_univ_of_connected hconnected v]
  exact Set.infinite_univ

lemma criticalProbability_le_of_pos {p : unitInterval}
    (hp : 0 < G.law p G.percolates) : G.criticalProbability ≤ p :=
  sInf_le hp

lemma law_percolates_eq_zero_of_lt_critical {p : unitInterval}
    (hp : p < G.criticalProbability) : G.law p G.percolates = 0 := by
  by_contra h
  exact (not_le_of_gt hp) (G.criticalProbability_le_of_pos (pos_iff_ne_zero.mpr h))

lemma cluster_subset_endpoints (ω : Set E) (v : V) :
    G.cluster ω v ⊆ insert v {w | ∃ e ∈ ω, w ∈ G.ends e} := by
  intro w hw
  have h := ((G.openGraph ω).reachable_iff_reflTransGen v w).mp hw
  clear hw
  induction h with
  | refl => exact Set.mem_insert _ _
  | @tail u w h huw _ =>
      obtain ⟨⟨e, he, heq⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huw
      exact Or.inr ⟨e, he, by simp [heq]⟩

lemma finite_cluster_of_finite_bonds {ω : Set E} (hω : ω.Finite) (v : V) :
    (G.cluster ω v).Finite := by
  classical
  have hf : {w | ∃ e ∈ ω, w ∈ G.ends e}.Finite := by
    have heq : {w | ∃ e ∈ ω, w ∈ G.ends e} =
        ⋃ e ∈ ω, (↑(G.ends e).toFinset : Set V) := by
      ext w
      simp
    rw [heq]
    exact hω.biUnion fun e _ => (G.ends e).toFinset.finite_toSet
  exact (hf.insert v).subset (G.cluster_subset_endpoints ω v)

lemma not_percolates_of_finite_bonds {ω : Set E} (hω : ω.Finite) :
    ω ∉ G.percolates := by
  rintro ⟨v, hv⟩
  exact hv (G.finite_cluster_of_finite_bonds hω v)

lemma mem_cluster_finite_witness {ω : Set E} {v w : V} (h : w ∈ G.cluster ω v) :
    ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ w ∈ G.cluster s v := by
  classical
  have hr := ((G.openGraph ω).reachable_iff_reflTransGen v w).mp h
  clear h
  induction hr with
  | refl => exact ⟨∅, Set.finite_empty, Set.empty_subset _, .refl _⟩
  | @tail u w hr huw ih =>
      obtain ⟨s, hs, hsω, hvs⟩ := ih
      obtain ⟨⟨e, heω, heq⟩, hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huw
      refine ⟨insert e s, hs.insert e, Set.insert_subset heω hsω, ?_⟩
      have hvu : (G.openGraph (insert e s)).Reachable v u :=
        hvs.mono (G.openGraph_mono (Set.subset_insert _ _))
      apply hvu.trans
      apply SimpleGraph.Adj.reachable
      exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e, Set.mem_insert _ _, heq⟩, hne⟩

lemma finite_subset_cluster_finite_witness {ω : Set E} {v : V} {K : Set V}
    (hK : K.Finite) (hKv : K ⊆ G.cluster ω v) :
    ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ K ⊆ G.cluster s v := by
  classical
  have h : ∀ w ∈ K, ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ w ∈ G.cluster s v :=
    fun w hw => G.mem_cluster_finite_witness (hKv hw)
  choose s hs hsω hws using h
  let := hK.fintype
  refine ⟨⋃ w : K, s w w.property, ?_, ?_, ?_⟩
  · exact Set.finite_iUnion fun w => hs w w.property
  · exact Set.iUnion_subset fun w => hsω w w.property
  · intro w hw
    exact G.cluster_mono (Set.subset_iUnion (fun w : K => s w w.property) ⟨w, hw⟩)
      v (hws w hw)

end BondGraph

namespace ClusterDeletion
variable {V : Type*}

def delete (H : SimpleGraph V) (U : Set V) : SimpleGraph V where
  Adj v w := H.Adj v w ∧ v ∉ U ∧ w ∉ U
  symm.symm _v _w h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl v h := H.loopless.irrefl v h.1

def roots (H : SimpleGraph V) (S : Set V) : Set V :=
  {v | ∃ s ∈ S, H.Reachable s v}

def component (H : SimpleGraph V) (s : V) : Set V :=
  {v | H.Reachable s v}

lemma delete_antitone (H : SimpleGraph V) {U U' : Set V} (h : U ⊆ U') :
    delete H U' ≤ delete H U :=
  fun _ _ hh => ⟨hh.1, fun hv => hh.2.1 (h hv), fun hw => hh.2.2 (h hw)⟩

lemma delete_le (H : SimpleGraph V) (U : Set V) : delete H U ≤ H :=
  fun _ _ h => h.1

lemma roots_mono {H H' : SimpleGraph V} (h : H ≤ H') (S : Set V) :
    roots H S ⊆ roots H' S := by
  rintro v ⟨s, hs, hsv⟩
  exact ⟨s, hs, hsv.mono h⟩

lemma component_mono {H H' : SimpleGraph V} (h : H ≤ H') (s : V) :
    component H s ⊆ component H' s :=
  fun _ hv => hv.mono h

lemma roots_self (H : SimpleGraph V) (S : Set V) : S ⊆ roots H S :=
  fun s hs => ⟨s, hs, .refl _⟩

lemma reachable_not_mem_roots {H : SimpleGraph V} {S : Set V} {s v : V}
    (hs : s ∉ roots H S) (hsv : H.Reachable s v) : v ∉ roots H S := by
  rintro ⟨u, hu, huv⟩
  exact hs ⟨u, hu, huv.trans hsv.symm⟩

lemma roots_closed {H : SimpleGraph V} {S : Set V} {v w : V}
    (hv : v ∈ roots H S) (hvw : H.Adj v w) : w ∈ roots H S := by
  obtain ⟨s, hs, hsv⟩ := hv
  exact ⟨s, hs, hsv.trans hvw.reachable⟩

lemma reachable_mem_of_closed {H : SimpleGraph V} {U : Set V}
    (hU : ∀ ⦃v w⦄, v ∈ U → H.Adj v w → w ∈ U) {s v : V}
    (hs : s ∈ U) (hsv : H.Reachable s v) : v ∈ U := by
  have hr := (H.reachable_iff_reflTransGen s v).mp hsv
  clear hsv
  induction hr with
  | refl => exact hs
  | tail _ huv ih => exact hU ih huv

lemma roots_subset_of_adj {H H' : SimpleGraph V} (S : Set V)
    (hh : ∀ ⦃v w⦄, v ∈ roots H S → H.Adj v w → H'.Adj v w) :
    roots H S ⊆ roots H' S := by
  rintro v ⟨s, hs, hsv⟩
  refine ⟨s, hs, ?_⟩
  have hr := (H.reachable_iff_reflTransGen s v).mp hsv
  clear hsv
  induction hr with
  | refl => exact .refl _
  | @tail u v hr huv ih =>
      exact ih.trans (hh ⟨s, hs, (H.reachable_iff_reflTransGen s u).mpr hr⟩ huv).reachable

lemma roots_eq_of_adj_eq_incident {H H' : SimpleGraph V} {S U : Set V}
    (hU : roots H S = U)
    (hh : ∀ ⦃v w⦄, v ∈ U → (H.Adj v w ↔ H'.Adj v w)) :
    roots H' S = U := by
  subst U
  apply Set.Subset.antisymm
  · rintro v ⟨s, hs, hsv⟩
    exact reachable_mem_of_closed
      (fun {_ _} hv hvw => roots_closed hv ((hh hv).mpr hvw)) (roots_self H S hs) hsv
  · exact roots_subset_of_adj S fun {_ _} hv hvw => (hh hv).mp hvw

lemma delete_roots_component (H : SimpleGraph V) (S : Set V) (s : V)
    (hs : s ∉ roots H S) :
    component (delete H (roots H S)) s = component H s := by
  apply Set.Subset.antisymm (component_mono (delete_le _ _) _)
  intro v hv
  have hr := (H.reachable_iff_reflTransGen s v).mp hv
  clear hv
  induction hr with
  | refl => exact .refl _
  | @tail u v hr huv ih =>
      have hsu : H.Reachable s u := (H.reachable_iff_reflTransGen _ _).mpr hr
      have hsv : H.Reachable s v := hsu.trans huv.reachable
      exact ih.trans (SimpleGraph.Adj.reachable
        ⟨huv, reachable_not_mem_roots hs hsu, reachable_not_mem_roots hs hsv⟩)

lemma delete_delete (H : SimpleGraph V) (U W : Set V) :
    delete (delete H U) W = delete H (W ∪ U) := by
  ext v w
  simp only [delete, Set.mem_union, not_or]
  tauto

lemma delete_roots_union_component (H : SimpleGraph V) (S U : Set V) (s : V)
    (hs : s ∉ roots (delete H U) S) :
    component (delete H (roots (delete H U) S ∪ U)) s = component (delete H U) s := by
  rw [← delete_delete]
  exact delete_roots_component _ _ _ hs

noncomputable def residual (H : SimpleGraph V) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) : ℝ := by
  classical
  exact if s ∉ roots (delete H U) S then
    F (component (delete H (roots (delete H U) S)) s) -
      F (component (delete H (roots (delete H U) S ∪ U)) s)
  else 0

lemma residual_nonneg (H : SimpleGraph V) (S : Set V) (s : V)
    {F : Set V → ℝ} (hF : Monotone F) (U : Set V) : 0 ≤ residual H S s F U := by
  classical
  unfold residual
  split_ifs
  · rfl
  · exact sub_nonneg.mpr (hF (component_mono (delete_antitone H Set.subset_union_left) s))

lemma residual_monotone (H : SimpleGraph V) (S : Set V) (s : V)
    {F : Set V → ℝ} (hF : Monotone F) : Monotone (residual H S s F) := by
  classical
  intro U U' hUU'
  have hW : roots (delete H U') S ⊆ roots (delete H U) S :=
    roots_mono (delete_antitone H hUU') S
  by_cases hs : s ∉ roots (delete H U) S
  · have hs' : s ∉ roots (delete H U') S := fun h => hs (hW h)
    rw [residual, ite_eq_left hs, residual, ite_eq_left hs']
    rw [delete_roots_union_component H S U s hs,
      delete_roots_union_component H S U' s hs']
    have hh₁ := hF (component_mono (delete_antitone H hW) s)
    have hh₂ := hF (component_mono (delete_antitone H hUU') s)
    exact sub_le_sub hh₁ hh₂
  · rw [residual, ite_eq_right hs]
    exact residual_nonneg H S s hF U'

end ClusterDeletion
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def incidentEdges (U : Set V) : Set E := {e | ∃ v ∈ U, v ∈ G.ends e}

lemma openGraph_adj_eq_of_incident {U : Set V} {ω ω' : Set E}
    (hω : ∀ e ∈ G.incidentEdges U, e ∈ ω ↔ e ∈ ω') {v w : V} (hv : v ∈ U) :
    (G.openGraph ω).Adj v w ↔ (G.openGraph ω').Adj v w := by
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  have he : ∀ e, G.ends e = s(v, w) → e ∈ G.incidentEdges U := by
    intro e heq
    exact ⟨v, hv, by simp [heq]⟩
  constructor
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).mp heω, heq⟩, hne⟩
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).mpr heω, heq⟩, hne⟩

lemma roots_eq_of_incident {S U : Set V} {ω ω' : Set E}
    (hU : ClusterDeletion.roots (G.openGraph ω) S = U)
    (hω : ∀ e ∈ G.incidentEdges U, e ∈ ω ↔ e ∈ ω') :
    ClusterDeletion.roots (G.openGraph ω') S = U :=
  ClusterDeletion.roots_eq_of_adj_eq_incident hU (fun {_ _} hv => G.openGraph_adj_eq_of_incident hω hv)

lemma dependsOn_exact_roots (S U : Set V) :
    DependsOn (fun ω : Set E => ClusterDeletion.roots (G.openGraph ω) S = U)
      (G.incidentEdges U) := by
  intro ω ω' hω
  apply propext
  exact ⟨fun h => G.roots_eq_of_incident h (fun e he => (hω e he).to_iff),
    fun h => G.roots_eq_of_incident h (fun e he => (hω e he).symm.to_iff)⟩

lemma delete_openGraph_dependsOn (U : Set V) :
    DependsOn (fun ω : Set E => ClusterDeletion.delete (G.openGraph ω) U)
      (G.incidentEdges U)ᶜ := by
  intro ω ω' hω
  ext v w
  change ((G.openGraph ω).Adj v w ∧ v ∉ U ∧ w ∉ U) ↔
    ((G.openGraph ω').Adj v w ∧ v ∉ U ∧ w ∉ U)
  by_cases hv : v ∈ U
  · simp [hv]
  by_cases hw : w ∈ U
  · simp [hw]
  simp only [hv, hw, not_false_eq_true, and_self, and_true, openGraph,
    SimpleGraph.fromEdgeSet_adj]
  have he : ∀ e, G.ends e = s(v, w) → e ∈ (G.incidentEdges U)ᶜ := by
    intro e heq
    rintro ⟨x, hxU, hxe⟩
    have := hxe
    simp only [heq, Sym2.mem_iff] at this
    rcases this with rfl | rfl
    · exact hv hxU
    · exact hw hxU
  constructor
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).to_iff.mp heω, heq⟩, hne⟩
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).to_iff.mpr heω, heq⟩, hne⟩

lemma deleted_roots_eq_of_incident {S U W : Set V} {ω ω' : Set E}
    (hW : ClusterDeletion.roots (ClusterDeletion.delete (G.openGraph ω) U) S = W)
    (hω : ∀ e ∈ G.incidentEdges W, e ∈ ω ↔ e ∈ ω') :
    ClusterDeletion.roots (ClusterDeletion.delete (G.openGraph ω') U) S = W := by
  apply ClusterDeletion.roots_eq_of_adj_eq_incident hW
  intro v v' hv
  change ((G.openGraph ω).Adj v v' ∧ v ∉ U ∧ v' ∉ U) ↔
    ((G.openGraph ω').Adj v v' ∧ v ∉ U ∧ v' ∉ U)
  rw [G.openGraph_adj_eq_of_incident hω hv]

lemma dependsOn_exact_deleted_roots (S U W : Set V) :
    DependsOn (fun ω : Set E =>
      ClusterDeletion.roots (ClusterDeletion.delete (G.openGraph ω) U) S = W)
      (G.incidentEdges W) := by
  intro ω ω' hω
  apply propext
  exact ⟨fun h => G.deleted_roots_eq_of_incident h (fun e he => (hω e he).to_iff),
    fun h => G.deleted_roots_eq_of_incident h (fun e he => (hω e he).symm.to_iff)⟩

end BondGraph
end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
