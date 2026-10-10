import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.PowersetCardTriple

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma incidentTriangle_third {n : ℕ} {G : Graph n} {u v : Fin n}
    (huv : u ≠ v) {t : Finset (Fin n)} (ht : t ∈ incidentTriangles G {u,v}) :
    ∃ w ∈ commonNeighbors G u v, t = {u,v,w} ∧ u ≠ w ∧ v ≠ w := by
  obtain ⟨ht,hpair⟩ := Finset.mem_filter.mp ht
  obtain ⟨htcard,htG⟩ := mem_triangles.mp ht
  have hsub : ({u,v} : Finset (Fin n)) ⊆ t := (Finset.mem_powersetCard.mp hpair).1
  have hc : (t \ {u,v}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, htcard, Finset.card_pair huv]
  obtain ⟨w,heq⟩ := Finset.card_eq_one.mp hc
  have hw : w ∈ t \ {u,v} := by rw [heq]; simp
  obtain ⟨hwt,hwuv⟩ := Finset.mem_sdiff.mp hw
  have huw : u ≠ w := by intro h; apply hwuv; simp [h]
  have hvw : v ≠ w := by intro h; apply hwuv; simp [h]
  have htriple : t = {u,v,w} := by
    have hu := Finset.sdiff_union_of_subset hsub
    rw [heq] at hu
    rw [← hu]
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hcw : w ∈ commonNeighbors G u v := by
    apply (mem_commonNeighbors G u v w).mpr
    constructor
    · apply htG
      apply Finset.mem_powersetCard.mpr
      exact ⟨by rw [htriple]; simp, Finset.card_pair huw⟩
    · apply htG
      apply Finset.mem_powersetCard.mpr
      exact ⟨by rw [htriple]; simp, Finset.card_pair hvw⟩
  exact ⟨w,hcw,htriple,huw,hvw⟩

lemma incidentTriangles_eq_image {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) {u v : Fin n} (he : {u,v} ∈ G) :
    incidentTriangles G {u,v} = (commonNeighbors G u v).image (fun w => {u,v,w}) := by
  have huv : u ≠ v := by
    intro h
    have hh := mem_completeGraph.mp (hG he)
    simp [h] at hh
  ext t
  constructor
  · intro ht
    obtain ⟨w,hw,rfl,_,_⟩ := incidentTriangle_third huv ht
    exact Finset.mem_image.mpr ⟨w,hw,rfl⟩
  · intro ht
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp ht
    apply Finset.mem_filter.mpr
    refine ⟨(triangle_closure_iff hG huv hw).mpr he,?_⟩
    exact Finset.mem_powersetCard.mpr ⟨by simp,Finset.card_pair huv⟩

theorem triangleDegree_eq_codegree {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) {u v : Fin n} (he : {u,v} ∈ G) :
    triangleDegree G {u,v} = currentCodegree G u v := by
  unfold triangleDegree currentCodegree
  rw [incidentTriangles_eq_image hG he]
  apply Finset.card_image_of_injOn
  intro a ha b _ hab
  change ({u,v,a} : Finset (Fin n)) = {u,v,b} at hab
  have ha' : a ∈ ({u,v,b} : Finset (Fin n)) := by rw [← hab]; simp
  have hnea := commonNeighbors_ne hG ha
  simpa [hnea.1.symm,hnea.2.symm] using ha'

theorem step_mean_codegree {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) (hQ : (triangles G).Nonempty)
    (u v : Fin n) (huv : u ≠ v) :
    pmfMean (step G) (fun H => (currentCodegree H u v : ℝ)) =
      (currentCodegree G u v : ℝ) -
      (∑ w ∈ commonNeighbors G u v,
        ((currentCodegree G u w : ℝ) + currentCodegree G v w -
          if {u,v} ∈ G then 1 else 0)) / (triangles G).card := by
  rw [step_mean_codegree_hazard G u v hQ]
  congr 2
  apply Finset.sum_congr rfl
  intro w hw
  rw [wedge_hazard_exact hG huv hw]
  have hw' := (mem_commonNeighbors G u v w).mp hw
  rw [triangleDegree_eq_codegree hG hw'.1, triangleDegree_eq_codegree hG hw'.2]
  simp only [triangle_closure_iff hG huv hw]

end SharpTerminalLeave

end
end

end OAI
