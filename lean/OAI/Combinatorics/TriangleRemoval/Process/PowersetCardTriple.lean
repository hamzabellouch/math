import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.CommonNeighborsMono

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma powersetCard_triple {α : Type*} [DecidableEq α] {u v w : α}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ({u,v,w} : Finset α).powersetCard 2 = {{u,v},{u,w},{v,w}} := by
  have h2 : ({v,w}:Finset α).powersetCard 2 = {{v,w}} := by
    rw [← Finset.card_pair hvw]
    exact Finset.powersetCard_self _
  rw [Finset.powersetCard_succ_insert (by simp [huv,huw]) 1, h2]
  simp only [Finset.powersetCard_one, Finset.map_insert, Finset.map_singleton, Finset.image_insert,
    Finset.image_singleton, Function.Embedding.coeFn_mk]
  ext s
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

lemma triangle_closure_iff {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    {u v w : Fin n} (huv : u ≠ v) (hw : w ∈ commonNeighbors G u v) :
    {u,v,w} ∈ triangles G ↔ {u,v} ∈ G := by
  obtain ⟨huw,hvw⟩ := commonNeighbors_ne hG hw
  obtain ⟨huwG,hvwG⟩ := (mem_commonNeighbors G u v w).mp hw
  rw [mem_triangles, powersetCard_triple huv huw hvw]
  simp [huv,huw,hvw,Finset.insert_subset_iff,Finset.singleton_subset_iff,huwG,hvwG]

theorem codegree_step_range {n : ℕ} {G H : Graph n} (hG : G ⊆ completeGraph n)
    (u v : Fin n) (hH : H ∈ (step G).support) :
    0 ≤ (currentCodegree G u v : ℝ) - currentCodegree H u v ∧
      (currentCodegree G u v : ℝ) - currentCodegree H u v ≤ 2 := by
  by_cases h : (triangles G).Nonempty
  · obtain ⟨t,ht,rfl⟩ := (step_support_active h).mp hH
    exact codegree_delete_range hG u v ht
  · rw [step, dite_eq_right h, PMF.mem_support_pure_iff] at hH
    subst H
    norm_num

theorem codegree_step_second_moment {n : ℕ} {G : Graph n}
    (hG : G ⊆ completeGraph n) (u v : Fin n) :
    pmfMean (step G) (fun H =>
      ((currentCodegree H u v : ℝ) - currentCodegree G u v)^2) ≤
        2 * ((currentCodegree G u v : ℝ) -
          pmfMean (step G) (fun H => (currentCodegree H u v : ℝ))) := by
  calc
    _ ≤ pmfMean (step G) (fun H =>
        2 * ((currentCodegree G u v : ℝ) - currentCodegree H u v)) := by
      apply pmfMean_mono
      intro H hH
      obtain ⟨hlo,hhi⟩ := codegree_step_range hG u v hH
      nlinarith
    _ = _ := by rw [pmfMean_const_mul, pmfMean_sub, pmfMean_const]

end SharpTerminalLeave

end
end

end OAI
