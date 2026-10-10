import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import OAI.Probability.CriticalPercolation.Criticality.OpenRay
import OAI.Probability.CriticalPercolation.GraphGeometry.InducedCritical

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma image_restrict (S : Set V) (ω : Set E) :
    Subtype.val '' (Subtype.val ⁻¹' ω : Set (G.inducedEdges S))=ω∩G.inducedEdges S := by
  ext e
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨ha,a.property⟩
  · rintro ⟨he,hs⟩
    exact ⟨⟨e,hs⟩,he,rfl⟩

def domainComponent (S : Set V) (o : V) : Set V := G.cluster (G.inducedEdges S) o

lemma domainComponent_subset {S : Set V} {o : V} (ho : o∈S) :
    G.domainComponent S o⊆S := by
  have h := G.induced_cluster_subset S Set.univ (⟨o,ho⟩ : S)
  simpa only [Set.image_univ,Subtype.range_coe,domainComponent] using h

lemma domainComponent_self (S : Set V) (o : V) : o∈G.domainComponent S o :=
  SimpleGraph.Reachable.refl o

lemma domainComponent_closed (S : Set V) (o : V) {x y : V}
    (hx : x∈G.domainComponent S o) (hxy : (G.openGraph (G.inducedEdges S)).Adj x y) :
    y∈G.domainComponent S o := hx.trans hxy.reachable

lemma domainComponent_connected (S : Set V) (o : V) :
    (G.induce (G.domainComponent S o)).fullGraph.Connected := by
  let C := G.domainComponent S o
  let a : C := ⟨o,G.domainComponent_self S o⟩
  have hreach : ∀ x : C, ((G.induce C).fullGraph).Reachable a x := by
    intro x
    apply (G.induce_reachable C Set.univ a x).mpr
    rw [Set.image_univ,Subtype.range_coe]
    have h : (G.openGraph (G.inducedEdges S)).Reachable o x.val := x.property
    rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
    have H : ∀ y, Relation.ReflTransGen (G.openGraph (G.inducedEdges S)).Adj o y →
        Relation.ReflTransGen (G.openGraph (G.inducedEdges C)).Adj o y := by
      intro y hy
      induction hy with
      | refl => exact .refl
      | @tail b c hr hadj ih =>
        have hb : b∈C := (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hr
        have hc : c∈C := G.domainComponent_closed S o hb hadj
        obtain ⟨⟨e,he,hend⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hadj
        have hC : e∈G.inducedEdges C := by
          intro v hv
          rw [hend] at hv
          rcases Sym2.mem_iff.mp hv with rfl|rfl
          · exact hb
          · exact hc
        exact ih.tail ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,hC,hend⟩,hne⟩)
    exact H _ h
  exact (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨a,hreach⟩

lemma OpenRay.reachable_start {ω : Set E} (r : G.OpenRay ω) (n : ℕ) :
    (G.openGraph ω).Reachable (r.vertex 0) (r.vertex n) := by
  induction n with
  | zero => exact .refl _
  | succ n ih => exact ih.trans (r.adjacent n).reachable

lemma OpenRay.percolates {ω : Set E} (r : G.OpenRay ω) : ω∈G.percolates := by
  refine ⟨r.vertex 0,?_⟩
  exact (Set.infinite_range_of_injective r.injective).mono (by
    rintro x ⟨n,rfl⟩
    exact r.reachable_start G n)

def OpenRay.induce {ω : Set E} (r : G.OpenRay ω) (S : Set V)
    (hS : ∀ n, r.vertex n∈S) :
    (G.induce S).OpenRay (Subtype.val ⁻¹' ω) where
  vertex n := ⟨r.vertex n,hS n⟩
  injective := fun _ _ h => r.injective (congrArg Subtype.val h)
  adjacent n := by
    apply (G.induce_adj S (Subtype.val ⁻¹' ω) _ _).mpr
    rw [G.image_restrict]
    exact (G.open_induced_adj S ω _ _).mpr ⟨r.adjacent n,hS n,hS (n+1)⟩

lemma OpenRay.mem_domainComponent {ω : Set E} (r : G.OpenRay ω) (S : Set V)
    (hS : ∀ n, r.vertex n∈S) (n : ℕ) :
    r.vertex n∈G.domainComponent S (r.vertex 0) := by
  induction n with
  | zero => exact G.domainComponent_self S _
  | succ n ih =>
    apply G.domainComponent_closed S _ ih
    apply G.openGraph_mono Set.inter_subset_right
    exact (G.open_induced_adj S ω _ _).mpr ⟨r.adjacent n,hS n,hS (n+1)⟩

lemma ae_restriction_not_percolates [Countable V] [Countable E]
    (S : Set V) (p : unitInterval) (h : (G.induce S).law p (G.induce S).percolates=0) :
    ∀ᵐ ω ∂G.law p, Subtype.val ⁻¹' ω∉(G.induce S).percolates := by
  rw [←G.law_induce S p,Measure.map_apply] at h
  · apply ae_iff.mpr
    convert h using 1
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_preimage,not_not]
  · exact Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  · exact (G.induce S).measurableSet_percolates

theorem bounded_ray_critical_component [Countable V] [Countable E]
    (u v : V → ℝ)
    (hbad : ¬∀ᵐ ω ∂G.law G.criticalProbability,
      ¬∃ r : G.OpenRay ω, ∃ U W : ℝ,
        ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W) :
    ∃ (k : ℕ) (o : V),
      let S := {x | |u x|≤(k:ℝ) ∧ |v x|≤(k:ℝ)}
      o∈S ∧
      let H := G.induce (G.domainComponent S o)
      H.criticalProbability=G.criticalProbability ∧
      0<H.law H.criticalProbability H.percolates := by
  let S : ℕ → Set V := fun k => {x | |u x|≤(k:ℝ) ∧ |v x|≤(k:ℝ)}
  have hex : ∃ (k : ℕ) (o : V), o∈S k ∧
      0<(G.induce (G.domainComponent (S k) o)).law G.criticalProbability
        (G.induce (G.domainComponent (S k) o)).percolates := by
    by_contra hh
    push Not at hh
    have ha : ∀ k o, ∀ᵐ ω ∂G.law G.criticalProbability,
        o∈S k → Subtype.val ⁻¹' ω∉(G.induce (G.domainComponent (S k) o)).percolates := by
      intro k o
      by_cases ho : o∈S k
      · exact (G.ae_restriction_not_percolates _ _ (le_antisymm (hh k o ho) bot_le)).mono
          (fun _ h _ => h)
      · exact Filter.Eventually.of_forall (fun _ h => (ho h).elim)
    have hall : ∀ᵐ ω ∂G.law G.criticalProbability, ∀ k o,
        o∈S k → Subtype.val ⁻¹' ω∉(G.induce (G.domainComponent (S k) o)).percolates :=
      (ae_all_iff.mpr fun k => ae_all_iff.mpr (ha k))
    apply hbad
    filter_upwards [hall] with ω hω
    rintro ⟨r,U,W,hr⟩
    obtain ⟨k,hk⟩ := exists_nat_ge (max U W)
    have hrS : ∀ n, r.vertex n∈S k := fun n =>
      ⟨(hr n).1.trans ((le_max_left _ _).trans hk),
       (hr n).2.trans ((le_max_right _ _).trans hk)⟩
    exact hω k (r.vertex 0) (hrS 0)
      ((r.induce G _ (r.mem_domainComponent G _ hrS)).percolates _)
  obtain ⟨k,o,ho,hp⟩ := hex
  have heq := G.induce_criticalProbability_eq_of_pos (G.domainComponent (S k) o) hp
  exact ⟨k,o,ho,heq,by rwa [heq]⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
