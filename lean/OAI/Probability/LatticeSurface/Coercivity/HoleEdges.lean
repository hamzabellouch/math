import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.BadClusters
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleSize
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims
import OAI.Probability.LatticeSurface.Coercivity.OuterHulls

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

open scoped BigOperators

abbrev Edge := Sym2 Vertex

def neighbors (x : Vertex) : Finset Vertex :=
  {(x.1+1,x.2),(x.1-1,x.2),(x.1,x.2+1),(x.1,x.2-1)}

lemma mem_neighbors (x y : Vertex) : y∈neighbors x ↔ grid.Adj x y := by
  constructor
  · intro h
    simp only [neighbors,Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl|rfl|rfl
    · exact adj_right _ _
    · simpa using (adj_right (x.1-1) x.2).symm
    · exact adj_up _ _
    · simpa using (adj_up x.1 (x.2-1)).symm
  · intro h
    simpa only [neighbors,Finset.mem_insert,Finset.mem_singleton] using adj_cases h

lemma neighbors_card (x : Vertex) : (neighbors x).card ≤ 4 := by
  classical
  exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
    (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))))

noncomputable def edgesAt (x : Vertex) : Finset Edge := by
  classical
  exact (neighbors x).image (fun y => s(x,y))

lemma edgesAt_card (x : Vertex) : (edgesAt x).card ≤ 4 :=
  Finset.card_image_le.trans (neighbors_card x)

lemma edgeAt_self {x y : Vertex} (h : grid.Adj x y) : s(x,y)∈edgesAt x := by
  classical
  exact Finset.mem_image.mpr ⟨y,(mem_neighbors x y).mpr h,rfl⟩

lemma mem_edgesAt (e : Edge) (x : Vertex) :
    e∈edgesAt x ↔ e∈grid.edgeSet ∧ x∈e := by
  classical
  induction e using Sym2.inductionOn with
  | _ a b =>
    constructor
    · rintro h
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp h
      have hxy := (mem_neighbors x y).mp hy
      rw [← he]
      exact ⟨hxy,by simp⟩
    · rintro ⟨hab,hx⟩
      rcases Sym2.mem_iff.mp hx with rfl|rfl
      · exact edgeAt_self hab
      · simpa only [Sym2.eq_swap] using edgeAt_self (SimpleGraph.Adj.symm hab)

noncomputable def incidentEdges (H : Finset Vertex) : Finset Edge := by
  classical
  exact H.biUnion edgesAt

lemma mem_incidentEdges (H : Finset Vertex) (e : Edge) :
    e∈incidentEdges H ↔ e∈grid.edgeSet ∧ ∃ x∈H, x∈e := by
  classical
  simp only [incidentEdges,Finset.mem_biUnion,mem_edgesAt]
  aesop

lemma incidentEdges_card (H : Finset Vertex) : (incidentEdges H).card ≤ 4*H.card := by
  classical
  calc
    _ ≤ ∑ x∈H, (edgesAt x).card := Finset.card_biUnion_le
    _ ≤ ∑ _∈H, 4 := Finset.sum_le_sum fun x hx => edgesAt_card x
    _ = _ := by simp [Nat.mul_comm]

noncomputable def rimFin (H : Finset Vertex) : Finset Vertex := (rim_finite_bound H).choose

lemma coe_rimFin (H : Finset Vertex) : (rimFin H:Set Vertex)=rim H :=
  (rim_finite_bound H).choose_spec.1

lemma mem_rimFin (H : Finset Vertex) (x : Vertex) : x∈rimFin H ↔ x∈rim H := by
  change x∈(rimFin H:Set Vertex) ↔ _
  rw [coe_rimFin]

noncomputable def rimEdges (H : Finset Vertex) : Finset Edge := by
  classical
  exact (incidentEdges (rimFin H)).filter (fun e => e∈(rimNet H).edgeSet ∧ ∀ z∈e, z∈rim H)

lemma mem_rimEdges (H : Finset Vertex) (e : Edge) :
    e∈rimEdges H ↔ e∈(rimNet H).edgeSet ∧ ∀ z∈e, z∈rim H := by
  classical
  simp only [rimEdges,Finset.mem_filter]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    apply (mem_incidentEdges _ _).mpr
    exact ⟨h.1.1,x,(mem_rimFin H x).mpr (h.2 x (by simp)),by simp⟩

lemma rim_walk_edges {H : Finset Vertex} {x y : Vertex} (p : (rimNet H).Walk x y)
    (hp : ∀ z∈p.support, z∈rim H) : p.edges.toFinset ⊆ rimEdges H := by
  classical
  intro e he
  have he' := List.mem_toFinset.mp he
  exact (mem_rimEdges H e).mpr ⟨p.edges_subset_edgeSet he',
    fun z hz => hp z (p.mem_support_of_mem_edges he' hz)⟩

noncomputable def edgeAbs (u : Vertex → ℝ) : Edge → ℝ :=
  Sym2.lift ⟨(fun x y => |u y-u x|),fun _ _ => abs_sub_comm _ _⟩

@[simp] lemma edgeAbs_mk (u : Vertex → ℝ) (x y : Vertex) : edgeAbs u s(x,y)=|u y-u x| := rfl

lemma edgeAbs_nonneg (u : Vertex → ℝ) (e : Edge) : 0 ≤ edgeAbs u e := by
  induction e using Sym2.inductionOn with
  | _ x y => exact abs_nonneg _

lemma walk_telescope {G : SimpleGraph Vertex} (u : Vertex → ℝ)
    {x y : Vertex} (p : G.Walk x y) : |u y-u x| ≤ (p.edges.map (edgeAbs u)).sum := by
  induction p with
  | nil => simp
  | @cons x z y hxz p ih =>
    simp only [SimpleGraph.Walk.edges_cons,List.map_cons,List.sum_cons,edgeAbs_mk]
    calc
      |u y-u x| ≤ |u z-u x|+|u y-u z| := by
        calc
          |u y-u x| = |(u z-u x)+(u y-u z)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      _ ≤ |u z-u x|+(p.edges.map (edgeAbs u)).sum := add_le_add (le_refl _) ih

lemma path_power {G : SimpleGraph Vertex} (u : Vertex → ℝ) (p : ℝ) (hp : 1 ≤ p)
    {x y : Vertex} (w : G.Walk x y) (hw : w.IsPath) :
    |u y-u x|^p ≤ (w.length:ℝ)^(p-1) * ∑ e∈w.edges.toFinset, (edgeAbs u e)^p := by
  classical
  have hn := SimpleGraph.Walk.edges_nodup_of_support_nodup hw.support_nodup
  have ht : |u y-u x| ≤ ∑ e∈w.edges.toFinset, edgeAbs u e := by
    rw [List.sum_toFinset _ hn]
    exact walk_telescope u w
  refine (Real.rpow_le_rpow (abs_nonneg _) ht (by linarith)).trans ?_
  have hh := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg w.edges.toFinset hp
    (fun e he => edgeAbs_nonneg u e)
  have hcard : w.edges.toFinset.card=w.length := by
    rw [List.toFinset_card_of_nodup hn,SimpleGraph.Walk.length_edges]
  simpa only [hcard] using hh

lemma rim_power (H : Finset Vertex) (u : Vertex → ℝ) (p : ℝ) (hp : 1 ≤ p)
    {x y : Vertex} (w : (rimNet H).Walk x y)
    (hw : ∀ z∈w.support, z∈rim H) (hlen : w.length ≤ 8*H.card) :
    |u y-u x|^p ≤ (8*(H.card:ℝ))^(p-1) * ∑ e∈rimEdges H, (edgeAbs u e)^p := by
  classical
  have hb := w.bypass_isPath
  have hsup : ∀ z∈w.bypass.support, z∈rim H := fun z hz => hw z (w.support_bypass_subset_support hz)
  refine (path_power u p hp w.bypass hb).trans ?_
  apply mul_le_mul
  · apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    exact_mod_cast (w.length_bypass_le_length.trans hlen)
  · exact Finset.sum_le_sum_of_subset_of_nonneg (rim_walk_edges w.bypass hsup)
      (fun e he hne => Real.rpow_nonneg (edgeAbs_nonneg u e) _)
  · exact Finset.sum_nonneg fun e he => Real.rpow_nonneg (edgeAbs_nonneg u e) _
  · positivity

end SparseHoles

end

end OAI
