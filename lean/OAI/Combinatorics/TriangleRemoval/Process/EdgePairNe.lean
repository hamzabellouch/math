import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.PowersetCardTriple
import OAI.Combinatorics.TriangleRemoval.Spectral.LinkStarMatrix
import OAI.Combinatorics.TriangleRemoval.Spectral.ExtendStarApply

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma edge_pair_ne {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v : Fin n} (h : {u,v} ∈ G) : u ≠ v := by
  intro he
  have hh := mem_completeGraph.mp (hG h)
  simp [he] at hh

lemma star_pair_triangle_iff {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    (u : Fin n) (v w : neighbors G u) :
    ({u,v.val} : Finset (Fin n)) ≠ {u,w.val} ∧
      ({u,v.val} ∪ {u,w.val} : Finset (Fin n)) ∈ triangles G ↔ {v.val,w.val} ∈ G := by
  have hv : ({u,v.val} : Finset (Fin n)) ∈ G := (Finset.mem_filter.mp v.property).2
  have hw : ({u,w.val} : Finset (Fin n)) ∈ G := (Finset.mem_filter.mp w.property).2
  have huv := edge_pair_ne hG hv
  have huw := edge_pair_ne hG hw
  have hu : ({u,v.val} ∪ {u,w.val} : Finset (Fin n)) = {u,v.val,w.val} := by
    ext x; simp
  rw [hu]
  constructor
  · rintro ⟨hne,ht⟩
    have hvw : v.val ≠ w.val := by intro he; exact hne (by rw [he])
    exact (mem_triangles.mp ht).2 (Finset.mem_powersetCard.mpr
      ⟨by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢; tauto,
        Finset.card_pair hvw⟩)
  · intro hvw
    constructor
    · intro he
      have hh : v.val = w.val := congrArg Subtype.val
        (neighborEdge_injective G u (a₁ := v) (a₂ := w) (by
          apply Subtype.ext; apply Subtype.ext; exact he))
      exact edge_pair_ne hG hvw hh
    · exact (triangle_closure_iff hG huv
        ((mem_commonNeighbors G u v.val w.val).mpr ⟨hw,hvw⟩)).mpr hv

lemma extended_link_entry {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u : Fin n) (e f : G) :
    extendStar (edgeStar G u) (linkStarMatrix G hG u) e f =
      if u ∈ e.val ∧ u ∈ f.val ∧ e ≠ f ∧ e.val ∪ f.val ∈ triangles G then 1 else 0 := by
  classical
  by_cases he : e ∈ edgeStar G u
  · by_cases hf : f ∈ edgeStar G u
    · let v := (neighborEdgeEquiv G hG u).symm ⟨e,he⟩
      let w := (neighborEdgeEquiv G hG u).symm ⟨f,hf⟩
      have hev : (neighborEdge G u v).val = e := by
        exact congrArg Subtype.val ((neighborEdgeEquiv G hG u).apply_symm_apply ⟨e,he⟩)
      have hfw : (neighborEdge G u w).val = f := by
        exact congrArg Subtype.val ((neighborEdgeEquiv G hG u).apply_symm_apply ⟨f,hf⟩)
      rw [extendStar_apply,dite_eq_left he,dite_eq_left hf]
      change (if {v.val,w.val} ∈ G then (1 : ℝ) else 0) = _
      have her : u ∈ e.val := (mem_edgeStar _ _ _).mp he
      have hfr : u ∈ f.val := (mem_edgeStar _ _ _).mp hf
      simp only [her,hfr,true_and]
      congr 1
      rw [← hev,← hfw]
      apply propext
      change ({v.val,w.val} ∈ G) ↔
        ((⟨{u,v.val},_⟩ : G) ≠ ⟨{u,w.val},_⟩ ∧ ({u,v.val} ∪ {u,w.val}) ∈ triangles G)
      simpa only [ne_eq,Subtype.mk.injEq] using (star_pair_triangle_iff hG u v w).symm
    · have hfr : u ∉ f.val := by simpa only [mem_edgeStar] using hf
      simp [extendStar_apply,hf,hfr]
  · have her : u ∉ e.val := by simpa only [mem_edgeStar] using he
    simp [extendStar_apply,he,her]

theorem globalLinkAdjacency_entry {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (e f : G) : globalLinkAdjacency G hG e f =
      if e ≠ f ∧ e.val ∪ f.val ∈ triangles G then 1 else 0 := by
  classical
  simp only [globalLinkAdjacency,Matrix.sum_apply,extended_link_entry]
  by_cases hh : e ≠ f ∧ e.val ∪ f.val ∈ triangles G
  · have he := mem_completeGraph.mp (hG e.property)
    have hf := mem_completeGraph.mp (hG f.property)
    have hu := (mem_triangles.mp hh.2).1
    have hc := Finset.card_union_add_card_inter e.val f.val
    have hi : (e.val ∩ f.val).card = 1 := by omega
    have hs : ∑ u : Fin n, (if u ∈ e.val ∧ u ∈ f.val then (1 : ℝ) else 0) = 1 := by
      simp only [← Finset.mem_inter,Finset.sum_boole]
      have heq : Finset.univ.filter (fun u => u ∈ e.val ∩ f.val) = e.val ∩ f.val := by ext; simp
      rw [heq,hi]
      norm_num
    simpa [hh.1,hh.2] using hs
  · have hx : ∀ u, ¬(u ∈ e.val ∧ u ∈ f.val ∧ e ≠ f ∧ e.val ∪ f.val ∈ triangles G) :=
      fun _ h => hh h.2.2
    rw [ite_eq_right hh]
    calc
      _ = ∑ _u : Fin n, (0 : ℝ) := Finset.sum_congr rfl (fun u _ => ite_eq_right (hx u))
      _ = 0 := Finset.sum_const_zero

end SharpTerminalLeave

end

end OAI
