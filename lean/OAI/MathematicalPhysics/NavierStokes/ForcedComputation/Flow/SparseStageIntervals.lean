import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarSparseStages

namespace OAI

/-! The sparse anchor is constant between consecutive selected slots. -/

namespace ForcedComputation.PlanarRouting

open Finset

theorem stagesBefore_mono {m n : ℕ} (J : Fin m → Fin n) : Monotone (stagesBefore J) := by
  intro i j hij
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact hk.trans_le hij

theorem stagesBefore_between {m n : ℕ} {J : Fin m → Fin n} (hJ : StrictMono J)
    (k l : Fin m) (hkl : k.val + 1 = l.val) {i : ℕ}
    (hlo : (J k).val + 1 ≤ i) (hhi : i ≤ (J l).val) :
    stagesBefore J i = l.val := by
  have hlo' := stagesBefore_mono J hlo
  have hhi' := stagesBefore_mono J hhi
  rw [stagesBefore_selected_succ hJ k] at hlo'
  rw [stagesBefore_selected hJ l] at hhi'
  omega

theorem stagesBefore_before {m n : ℕ} {J : Fin m → Fin n} (hJ : StrictMono J)
    (k : Fin m) (hk : k.val = 0) {i : ℕ} (hi : i ≤ (J k).val) :
    stagesBefore J i = 0 := by
  have h := stagesBefore_mono J hi
  rw [stagesBefore_selected hJ k, hk] at h
  omega

theorem stagesBefore_after {m n : ℕ} {J : Fin m → Fin n} (hJ : StrictMono J)
    (k : Fin m) (hk : k.val + 1 = m) {i : ℕ} (hi : (J k).val + 1 ≤ i) :
    stagesBefore J i = m := by
  have h := stagesBefore_mono J hi
  rw [stagesBefore_selected_succ hJ k, hk] at h
  exact le_antisymm (stagesBefore_le J i) h

theorem sparseAnchor_of_count {E : Type*} {m n : ℕ} (J : Fin m → Fin n)
    (p : Fin (m + 1) → E) (i : ℕ) (k : Fin (m + 1))
    (hk : stagesBefore J i = k.val) : sparseAnchor J p i = p k := by
  unfold sparseAnchor
  apply congrArg p
  exact Fin.ext hk

end ForcedComputation.PlanarRouting

end OAI
