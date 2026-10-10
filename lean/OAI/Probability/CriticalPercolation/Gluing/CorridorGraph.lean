import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.CorridorSeparation
import OAI.Probability.CriticalPercolation.Gluing.CollarDistance
import OAI.Probability.CriticalPercolation.Gluing.OpenTrialBound
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma coordinate_ball_bound (f : V → ℝ) (ρ : ℝ) (hρ : 0≤ρ)
    (hf : ∀ ⦃v w⦄, G.fullGraph.Adj v w → |f v-f w|≤ρ)
    {v w : V} {n : ℕ} (hw : w∈G.vertexBall v n) : |f w-f v|≤n*ρ := by
  induction n generalizing w with
  | zero =>
    have he : w=v := hw
    subst w
    simp
  | succ n ih =>
    rcases hw with hw|hw
    · exact (ih hw).trans (by push_cast; nlinarith)
    · obtain ⟨u,hu,huw⟩ := Set.mem_iUnion₂.mp hw
      calc
        |f w-f v| ≤ |f w-f u|+|f u-f v| := abs_sub_le _ _ _
        _ ≤ ρ+n*ρ := add_le_add (hf huw.symm) (ih hu)
        _ = _ := by push_cast; ring

lemma coordinate_collar_bound (f : V → ℝ) (ρ : ℝ) (hρ : 0≤ρ)
    (hf : ∀ ⦃v w⦄, G.fullGraph.Adj v w → |f v-f w|≤ρ)
    (B : Set V) (c r : ℝ) (hB : ∀ v∈B, |f v-c|≤r)
    {w : V} {n : ℕ} (hw : w∈G.vertexCollar B n) : |f w-c|≤r+n*ρ := by
  obtain ⟨v,hv,hw⟩ := Set.mem_iUnion₂.mp hw
  calc
    |f w-c| ≤ |f w-f v|+|f v-c| := abs_sub_le _ _ _
    _ ≤ n*ρ+r := add_le_add (G.coordinate_ball_bound f ρ hρ hf hw) (hB v hv)
    _ = _ := add_comm _ _

lemma inducedEdges_inter (S T : Set V) :
    G.inducedEdges (S∩T)=G.inducedEdges S∩G.inducedEdges T := by
  ext e
  simp only [inducedEdges,Set.mem_ofPred_eq,Set.mem_inter_iff]
  exact ⟨fun h => ⟨fun v hv => (h v hv).1,fun v hv => (h v hv).2⟩,
    fun h v hv => ⟨h.1 v hv,h.2 v hv⟩⟩

lemma inducedEdges_mono {S T : Set V} (h : S⊆T) :
    G.inducedEdges S⊆G.inducedEdges T := by
  intro e he v hv
  exact h (he v hv)

end CriticalPercolation.BondGraph
namespace CriticalPercolation.Corridor
open BondGraph

variable {V E : Type*} (G : BondGraph V E) (ξ : V → Point) (j h : ℝ)

def graphBox (v : Site) : Set V := ξ ⁻¹' box j h v
def graphDomain (e : Edge) : Set V := ξ ⁻¹' domain j h e
def boxEdges (v : Site) : Set E := G.inducedEdges (graphBox ξ j h v)
def corridorEdges (e : Edge) : Set E := G.inducedEdges (graphDomain ξ j h e)

lemma graph_boxes_disjoint (hs : 2*j+h<1) {v w : Site} (hv : v≠w) :
    Disjoint (graphBox ξ j h v) (graphBox ξ j h w) :=
  (box_disjoint j h hs hv).preimage ξ

lemma graph_nonincident_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (hef : Disjoint (endpoints e) (endpoints f)) :
    Disjoint (graphDomain ξ j h e) (graphDomain ξ j h f) :=
  (nonincident_domains_disjoint j h hh hhj hs hef).preimage ξ

lemma edge_nonincident_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (hef : Disjoint (endpoints e) (endpoints f)) :
    Disjoint (corridorEdges G ξ j h e) (corridorEdges G ξ j h f) :=
  G.inducedEdges_disjoint (graph_nonincident_disjoint ξ j h hh hhj hs hef)

lemma shared_edges_in_box (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (hne : e≠f) {v : Site} (he : v∈endpoints e) (hf : v∈endpoints f) :
    corridorEdges G ξ j h e∩corridorEdges G ξ j h f⊆boxEdges G ξ j h v := by
  intro b hb w hw
  exact incident_domains_intersection j h hh hhj hs hne he hf
    ⟨hb.1 w hw,hb.2 w hw⟩

lemma edge_box_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e : Edge} {v : Site} (hv : v∉endpoints e) :
    Disjoint (boxEdges G ξ j h v) (corridorEdges G ξ j h e) :=
  G.inducedEdges_disjoint
    ((nonendpoint_domain_box_disjoint j h hh hhj hs hv).preimage ξ)

lemma history_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    (H : Set Edge) {e : Edge} (he : ∀ f∈H, Disjoint (endpoints f) (endpoints e)) :
    Disjoint (⋃ f∈H, corridorEdges G ξ j h f) (corridorEdges G ξ j h e) := by
  apply Set.disjoint_left.mpr
  intro b hb he'
  obtain ⟨f,hf,hb⟩ := Set.mem_iUnion₂.mp hb
  exact Set.disjoint_left.mp (edge_nonincident_disjoint G ξ j h hh hhj hs (he f hf)) hb he'

lemma history_intersection_subset (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    (H : Set Edge) {e : Edge} {v : Site}
    (he : e∉H) (hH : ∀ f∈H, endpoints f∩endpoints e⊆{v}) :
    (⋃ f∈H, corridorEdges G ξ j h f)∩corridorEdges G ξ j h e⊆boxEdges G ξ j h v := by
  intro b hb
  obtain ⟨f,hf,hbf⟩ := Set.mem_iUnion₂.mp hb.1
  have hne : f≠e := fun h => he (h ▸ hf)
  intro w hw
  obtain ⟨u,hu,hu',hwu⟩ := distinct_domains_intersection j h hh hhj hs hne
    (hbf w hw) (hb.2 w hw)
  have huv : u=v := hH f hf ⟨hu,hu'⟩
  rwa [huv] at hwu

end CriticalPercolation.Corridor
end
end
end

end OAI
