import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.BadClusters
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleEdges
import OAI.Probability.LatticeSurface.Coercivity.HoleExtension
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

noncomputable def activeHoles (L : Finset (Finset Vertex)) (E : Finset Edge) : Finset (Finset Vertex) := by
  classical
  exact L.filter (fun H => ∃ e∈E, ∃ z∈e,z∈H)

noncomputable def localEdges (L : Finset (Finset Vertex)) (E : Finset Edge) : Finset Edge := by
  classical
  exact E.filter (goodEdge (activeHoles L E)) ∪ (activeHoles L E).biUnion rimEdges

attribute [local instance] Classical.propDecidable

lemma HoleFamily.mono {L J : Finset (Finset Vertex)} (hL : HoleFamily L) (hJL : J ⊆ L) :
    HoleFamily J :=
  ⟨fun H hH => hL.nonempty H (hJL hH),
   fun H hH K hK hne => hL.disjoint H (hJL hH) K (hJL hK) hne,
   fun H hH K hK hne => hL.separated H (hJL hH) K (hJL hK) hne,
   fun H hH K hK => hL.rim_good H (hJL hH) K (hJL hK),
   fun H hH x hx y hy => hL.paths H (hJL hH) x hx y hy⟩

lemma active_subset (L : Finset (Finset Vertex)) (E : Finset Edge) : activeHoles L E ⊆ L :=
  Finset.filter_subset _ _

lemma active_mem (L : Finset (Finset Vertex)) (E : Finset Edge) {H : Finset Vertex}
    (hH : H∈L) {e : Edge} (he : e∈E) {z : Vertex} (hz : z∈e) (hzH : z∈H) : H∈activeHoles L E := by
  classical
  exact Finset.mem_filter.mpr ⟨hH,e,he,z,hz,hzH⟩

lemma active_fill (L : Finset (Finset Vertex)) (hL : HoleFamily L) (E : Finset Edge)
    {e : Edge} (he : e∈E) {z : Vertex} (hz : z∈e) :
    fillSite L z = fillSite (activeHoles L E) z := by
  classical
  by_cases h : ∃ H∈L,z∈H
  · obtain ⟨H,hH,hzH⟩ := h
    rw [fillSite_hole L hL hH hzH,
      fillSite_hole _ (hL.mono (active_subset L E)) (active_mem L E hH he hz hzH) hzH]
  · have hg : goodSite L z := by simpa only [goodSite,not_exists,not_and] using h
    rw [fillSite_good L hg,fillSite_good _ (fun H hH => hg H (active_subset L E hH))]

lemma active_edgeAbs (L : Finset (Finset Vertex)) (hL : HoleFamily L) (E : Finset Edge)
    (u : Vertex → ℝ) {e : Edge} (he : e∈E) :
    edgeAbs (extension L u) e=edgeAbs (extension (activeHoles L E) u) e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
    change |u (fillSite L y)-u (fillSite L x)|=|u (fillSite (activeHoles L E) y)-u (fillSite (activeHoles L E) x)|
    rw [active_fill L hL E he (by simp : y∈s(x,y)),active_fill L hL E he (by simp : x∈s(x,y))]

lemma weights_mono (L J : Finset (Finset Vertex)) (hJL : J ⊆ L) (p : ℝ) (e : Edge) :
    holeWeights J p e ≤ holeWeights L p e := by
  classical
  unfold holeWeights
  apply add_le_add_right
  apply Finset.sum_le_sum_of_subset_of_nonneg hJL
  intro H hH hnot
  split_ifs
  · exact holeCost_nonneg p H
  · exact le_refl _

lemma local_edges_good (L : Finset (Finset Vertex)) (hL : HoleFamily L)
    (E : Finset Edge) : ∀ e∈localEdges L E,goodEdge L e := by
  classical
  intro e he
  rcases Finset.mem_union.mp he with he|he
  · obtain ⟨he,hg⟩ := Finset.mem_filter.mp he
    refine ⟨hg.1,?_⟩
    intro z haz H hH hzH
    exact hg.2 z haz H (active_mem L E hH he haz hzH) hzH
  · obtain ⟨H,hH,he⟩ := Finset.mem_biUnion.mp he
    exact rim_edge_good L hL (active_subset L E hH) he

lemma local_energy_bound (L : Finset (Finset Vertex)) (hL : HoleFamily L)
    (u : Vertex → ℝ) (p : ℝ) (hp : 1 < p) (E : Finset Edge)
    (hE : ∀ e∈E,e∈grid.edgeSet) :
    (∑ e∈E,(edgeAbs (extension L u) e)^p) ≤
      ∑ e∈localEdges L E,holeWeights L p e*(edgeAbs u e)^p := by
  classical
  let J := activeHoles L E
  let F := localEdges L E
  have hJ : HoleFamily J := hL.mono (active_subset L E)
  have hr : ∀ H∈J,rimEdges H ⊆ F := by
    intro H hH e he;exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨H,hH,he⟩)
  calc
    _ = ∑ e∈E,(edgeAbs (extension J u) e)^p := Finset.sum_congr rfl (fun e he => congrArg (fun x : ℝ => x^p) (active_edgeAbs L hL E u he))
    _ ≤ ∑ e∈F,holeWeights J p e*(edgeAbs u e)^p := by
      rw [weighted_sum_identity J u p F hr]
      apply (extension_sum_bound J hJ u p hp E hE).trans
      apply add_le_add _ (le_refl _)
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun e he hne => Real.rpow_nonneg (edgeAbs_nonneg _ _) _)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_right (weights_mono L J (active_subset L E) p e) (Real.rpow_nonneg (edgeAbs_nonneg _ _) _)

lemma rim_in_buffer (L : Finset (Finset Vertex)) (N : ℕ) (hN : 1 ≤ N)
    {H : Finset Vertex} (hH : H∈L) {z : Vertex} (hz : z∈H)
    (hzQ : z∈box (0,0) (N,N)) (hd : siteDiameter L z ≤ N) :
    rim H ⊆ (box (-(2*N:ℤ),-(2*N:ℤ)) (3*N,3*N):Set Vertex) := by
  have hdH : diameter H ≤ N := by
    apply le_trans _ hd
    calc
      diameter H = (if incidentClosed H z then diameter H else 0) := (ite_eq_left (Or.inl hz)).symm
      _ ≤ siteDiameter L z := Finset.le_sup (f := fun H => if incidentClosed H z then diameter H else 0) hH
  intro y hy
  obtain ⟨_,x,hx,hy1,hy2⟩ := hy
  have hxz := le_diameter H hx hz
  have h1 := natAbs_sub_triangle y.1 x.1 z.1
  have h2 := natAbs_sub_triangle y.2 x.2 z.2
  have hh1 : (y.1-z.1).natAbs ≤ N+1 := by omega
  have hh2 : (y.2-z.2).natAbs ≤ N+1 := by omega
  rw [natAbs_sub_le_iff] at hh1 hh2
  have hzQ := mem_box.mp hzQ
  apply mem_box.mpr
  push_cast at *
  omega

lemma local_edges_buffer (L : Finset (Finset Vertex)) (hL : HoleFamily L)
    (N : ℕ) (hN : 1 ≤ N) (E : Finset Edge)
    (hQ : ∀ e∈E,∀ z∈e,z∈box (0,0) (N,N))
    (hd : ∀ z∈box (0,0) (N,N),siteDiameter L z ≤ N) :
    localEdges L E ⊆ incidentEdges (box (-(2*N:ℤ),-(2*N:ℤ)) (3*N,3*N)) := by
  classical
  intro e he
  have hg := (local_edges_good L hL E e he).1
  apply (mem_incidentEdges _ _).mpr
  refine ⟨hg,?_⟩
  rcases Finset.mem_union.mp he with he|he
  · have heE := (Finset.mem_filter.mp he).1
    induction e using Sym2.inductionOn with
    | _ x y =>
      refine ⟨x,?_,by simp⟩
      have hx := mem_box.mp (hQ _ heE x (by simp))
      apply mem_box.mpr
      omega
  · obtain ⟨H,hH,he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨hHL,e',heE,z,hze,hzH⟩ := Finset.mem_filter.mp hH
    have hr := rim_in_buffer L N hN hHL hzH (hQ e' heE z hze) (hd z (hQ e' heE z hze))
    have he := (mem_rimEdges H e).mp he
    induction e using Sym2.inductionOn with
    | _ x y => exact ⟨x,hr (he.2 x (by simp)),by simp⟩

lemma local_hole_energy (L : Finset (Finset Vertex)) (hL : HoleFamily L)
    (N : ℕ) (hN : 1 ≤ N) (u : Vertex → ℝ) (p : ℝ) (hp : 1 < p)
    (E : Finset Edge) (hE : ∀ e∈E,e∈grid.edgeSet)
    (hQ : ∀ e∈E,∀ z∈e,z∈box (0,0) (N,N))
    (hd : ∀ z∈box (0,0) (N,N),siteDiameter L z ≤ N) :
    let F := localEdges L E
    (∀ e∈F,goodEdge L e) ∧
    F ⊆ incidentEdges (box (-(2*N:ℤ),-(2*N:ℤ)) (3*N,3*N)) ∧
    (∑ e∈E,(edgeAbs (extension L u) e)^p) ≤ ∑ e∈F,holeWeights L p e*(edgeAbs u e)^p := by
  exact ⟨local_edges_good L hL E,local_edges_buffer L hL N hN E hQ hd,local_energy_bound L hL u p hp E hE⟩

end SparseHoles

end

end OAI
