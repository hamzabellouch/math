import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.IncidenceIdentity
import OAI.Probability.CriticalPercolation.Exploration.IncidenceDegree
import OAI.Probability.CriticalPercolation.Modular.ClusterDiscrepancy

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation
open FiniteProduct

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def openIncident (ω : Set E) (v : V) : Set E :=
  G.incidentEdges (G.cluster ω v) ∩ ω

lemma cluster_subset_endpoint_union (ω : Set E) (v : V) :
    G.cluster ω v ⊆ {v} ∪ ((fun e => (G.ends e).out.1) '' G.openIncident ω v ∪
      (fun e => (G.ends e).out.2) '' G.openIncident ω v) := by
  intro z hz
  change (G.openGraph ω).Reachable v z at hz
  rw [SimpleGraph.reachable_iff_reflTransGen] at hz
  induction hz with
  | refl => exact Or.inl rfl
  | @tail u z hv hu _ =>
    obtain ⟨⟨e,he,heq⟩,_⟩ := hu
    have hzmem : z ∈ G.ends e := by rw [heq]; simp
    have heI : e ∈ G.openIncident ω v := by
      exact ⟨⟨u,(SimpleGraph.reachable_iff_reflTransGen _ _).mpr hv,
        by rw [heq]; simp⟩,he⟩
    have hout : G.ends e = s((G.ends e).out.1,(G.ends e).out.2) :=
      (G.ends e).out_eq.symm
    rw [hout,Sym2.mem_iff] at hzmem
    exact Or.inr (hzmem.elim (fun h => Or.inl ⟨e,heI,h.symm⟩)
      (fun h => Or.inr ⟨e,heI,h.symm⟩))

lemma cluster_card_le_open_incident [Fintype V] [Fintype E] (ω : Set E) (v : V) :
    G.clusterSize ω v ≤ 1 + 2*(G.openIncident ω v).ncard := by
  calc
    _ ≤ ({v} ∪ ((fun e => (G.ends e).out.1) '' G.openIncident ω v ∪
      (fun e => (G.ends e).out.2) '' G.openIncident ω v)).ncard := by
      simpa only [clusterSize,← Set.ncard_eq_toFinset_card'] using
        Set.ncard_le_ncard (G.cluster_subset_endpoint_union ω v)
    _ ≤ ({v} : Set V).ncard + (((fun e => (G.ends e).out.1) '' G.openIncident ω v).ncard +
      ((fun e => (G.ends e).out.2) '' G.openIncident ω v).ncard) :=
      (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (Set.ncard_union_le _ _) _)
    _ ≤ _ := by
      have h1 := Set.ncard_image_le (s := G.openIncident ω v) (f := fun e => (G.ends e).out.1)
      have h2 := Set.ncard_image_le (s := G.openIncident ω v) (f := fun e => (G.ends e).out.2)
      simp only [Set.ncard_singleton]
      omega

lemma openIncident_card_centered [Fintype E] (p : ℝ) (ω : Set E) (v : V) :
    ((G.openIncident ω v).ncard : ℝ) = (IncidenceSearch.tree G v).centeredSum p ω +
      p*((IncidenceSearch.tree G v).queryCount ω : ℝ) := by
  rw [IncidenceSearch.tree_centered,IncidenceSearch.tree_count]
  simp only [Set.ncard_eq_toFinset_card']
  have ha : ((G.openIncident ω v).toFinset.card : ℝ) =
      ∑ e : E, if e ∈ G.openIncident ω v then (1:ℝ) else 0 := by simp
  have hb : ((G.incidentEdges (G.cluster ω v)).toFinset.card : ℝ) =
      ∑ e : E, if e ∈ G.incidentEdges (G.cluster ω v) then (1:ℝ) else 0 := by simp
  rw [ha,hb,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hi : e∈G.incidentEdges (G.cluster ω v) <;> by_cases ho : e∈ω <;>
    simp [openIncident,hi,ho]

lemma finite_susceptibility_bound [Fintype V] [Fintype E]
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (h0 : ∀ e, w e False=1-p) (h1 : ∀ e, w e True=p)
    (D : ℕ) (hD : ∀ v, (G.incidentEdges {v}).toFinset.card ≤ D)
    (hpD : 4*p*D ≤ 1) (v : V) :
    expect w (fun ω => (G.clusterSize {e | ω e} v : ℝ)) ≤ 2 := by
  let t := IncidenceSearch.tree G v
  let a := expect w (fun ω => (G.clusterSize {e | ω e} v : ℝ))
  have hmean := (t.centeredSum_moments ∅ (IncidenceSearch.tree_valid G v) p w hw
    (fun e _ => ⟨h0 e,h1 e⟩)).1
  have hquery : expect w (fun ω => (t.queryCount ω : ℝ)) ≤ D*a := by
    calc
      _ ≤ expect w (fun ω => (D:ℝ)*(G.clusterSize {e | ω e} v : ℝ)) := by
        apply expect_mono hn
        intro ω
        have hcount : t.queryCount ω = (G.incidentEdges (G.cluster {e | ω e} v)).toFinset.card :=
          IncidenceSearch.tree_count G v {e | ω e}
        rw [hcount]
        exact_mod_cast (by simpa only [clusterSize,mul_comm] using
          G.incident_card_le (G.cluster {e | ω e} v) D hD)
      _ = _ := expect_const_mul _ _ _
  have hcluster : a ≤ 1+2*p*(D*a) := by
    calc
      _ ≤ expect w (fun ω => 1+2*((G.openIncident {e | ω e} v).ncard : ℝ)) := by
        apply expect_mono hn
        intro ω
        exact_mod_cast G.cluster_card_le_open_incident {e | ω e} v
      _ = 1+2*p*expect w (fun ω => (t.queryCount ω : ℝ)) := by
        have hopen (ω : E → Prop) : ((G.openIncident {e | ω e} v).ncard : ℝ) =
            t.centeredSum p ω + p*(t.queryCount ω : ℝ) :=
          G.openIncident_card_centered p {e | ω e} v
        simp_rw [hopen]
        rw [expect_add,expect_const w hw,expect_const_mul,expect_add,hmean,
          expect_const_mul]
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hquery (mul_nonneg (by norm_num) hp.1 : 0≤2*p)
        linarith
  have ha : 0≤a := expect_nonneg hn (fun _ => Nat.cast_nonneg _)
  nlinarith

end BondGraph
end CriticalPercolation
end
end
end

end OAI
