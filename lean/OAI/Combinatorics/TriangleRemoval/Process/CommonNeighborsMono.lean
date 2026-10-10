import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.CommonNeighbors

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem commonNeighbors_mono {n : ℕ} {G H : Graph n} (h : H ⊆ G) (u v : Fin n) :
    commonNeighbors H u v ⊆ commonNeighbors G u v := by
  intro w hw
  exact (mem_commonNeighbors G u v w).mpr
    ⟨h ((mem_commonNeighbors H u v w).mp hw).1,
      h ((mem_commonNeighbors H u v w).mp hw).2⟩

theorem commonNeighbors_delete {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    (u v : Fin n) (t : Finset (Fin n)) :
    commonNeighbors (G \ t.powersetCard 2) u v =
      if u ∈ t ∨ v ∈ t then commonNeighbors G u v \ t else commonNeighbors G u v := by
  ext w
  by_cases hw : w ∈ commonNeighbors G u v
  · obtain ⟨huw,hvw⟩ := commonNeighbors_ne hG hw
    obtain ⟨he,hf⟩ := (mem_commonNeighbors G u v w).mp hw
    simp only [mem_commonNeighbors, Finset.mem_sdiff, he, hf, true_and,
      Finset.mem_powersetCard, Finset.insert_subset_iff, Finset.singleton_subset_iff,
      Finset.card_pair huw, Finset.card_pair hvw, and_true]
    split_ifs with ht <;> simp only [Finset.mem_sdiff, hw, true_and]
    · tauto
    · push Not at ht
      simp [ht.1, ht.2]
  · have hw' : w ∉ commonNeighbors (G \ t.powersetCard 2) u v :=
      fun hh => hw (commonNeighbors_mono Finset.sdiff_subset u v hh)
    split_ifs <;> simp [hw, hw']

theorem codegree_delete_range {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    (u v : Fin n) {t : Finset (Fin n)} (ht : t ∈ triangles G) :
    0 ≤ (currentCodegree G u v : ℝ) - currentCodegree (G \ t.powersetCard 2) u v ∧
      (currentCodegree G u v : ℝ) - currentCodegree (G \ t.powersetCard 2) u v ≤ 2 := by
  have hc : t.card = 3 := (mem_triangles.mp ht).1
  unfold currentCodegree
  rw [commonNeighbors_delete hG u v t]
  split_ifs with hp
  · have hbound : ((commonNeighbors G u v) ∩ t).card ≤ 2 := by
      rcases hp with hu | hv
      · have hsub : (commonNeighbors G u v) ∩ t ⊆ t.erase u := by
          intro w hw
          obtain ⟨hw,hwt⟩ := Finset.mem_inter.mp hw
          exact Finset.mem_erase.mpr ⟨(commonNeighbors_ne hG hw).1.symm,hwt⟩
        have hh := Finset.card_le_card hsub
        simpa [Finset.card_erase_of_mem hu, hc] using hh
      · have hsub : (commonNeighbors G u v) ∩ t ⊆ t.erase v := by
          intro w hw
          obtain ⟨hw,hwt⟩ := Finset.mem_inter.mp hw
          exact Finset.mem_erase.mpr ⟨(commonNeighbors_ne hG hw).2.symm,hwt⟩
        have hh := Finset.card_le_card hsub
        simpa [Finset.card_erase_of_mem hv, hc] using hh
    have hid := Finset.card_sdiff_add_card_inter (commonNeighbors G u v) t
    have hid' : ((commonNeighbors G u v \ t).card : ℝ) +
        ((commonNeighbors G u v ∩ t).card : ℝ) = (commonNeighbors G u v).card := by
      exact_mod_cast hid
    have hbound' : (((commonNeighbors G u v) ∩ t).card : ℝ) ≤ 2 := by exact_mod_cast hbound
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) ((commonNeighbors G u v ∩ t).card)]
  · simp

end SharpTerminalLeave

end
end

end OAI
