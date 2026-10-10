import OAI.Geometry.CylinderCovering.Radial.RiemannDefinitions

namespace OAI

open Set
namespace CylinderCovering.RadialPartitionCover

theorem exists_interval_in_chain (p : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : t ∈ Icc (p 0) (p N)) :
    ∃ i : ℕ, i < N ∧ t ∈ Icc (p i) (p (i + 1)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hzero : N = 0
    · subst N
      exact ⟨0, by omega, ht⟩
    · by_cases htN : t ≤ p N
      · obtain ⟨i, hi, hti⟩ := ih (Nat.pos_of_ne_zero hzero) ⟨ht.1, htN⟩
        exact ⟨i, Nat.lt_succ_of_lt hi, hti⟩
      · exact ⟨N, Nat.lt_succ_self N, ⟨(lt_of_not_ge htN).le, ht.2⟩⟩

theorem iUnion_intervals_eq (p : ℕ → ℝ) (hp : Monotone p)
    {N : ℕ} (hN : 0 < N) :
    (⋃ i : Fin N, Icc (p i) (p (i + 1))) = Icc (p 0) (p N) := by
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact ⟨(hp (Nat.zero_le i)).trans hi.1,
      hi.2.trans (hp (Nat.succ_le_of_lt i.isLt))⟩
  · intro ht
    obtain ⟨i, hi, hti⟩ := exists_interval_in_chain p hN ht
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hti⟩

open RadialRiemann

theorem equal_cells_cover {a b : ℝ} (hab : a ≤ b) {N : ℕ} (hN : 0 < N) :
    (⋃ i : Fin N, cell a b N i) = Icc a b := by
  have hd : 0 ≤ step a b N := div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg N)
  have hp : Monotone (point a b N) := by
    intro i j hij
    dsimp [point]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (show (i : ℝ) ≤ (j : ℝ) by exact_mod_cast hij) hd)
  have hlast : point a b N N = b := by
    have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
    dsimp [point, step]
    field_simp
    ring
  have h := iUnion_intervals_eq (point a b N) hp hN
  rw [hlast] at h
  simpa only [cell, point, Nat.cast_zero, zero_mul, add_zero] using h

theorem cell_subset_interval {a b : ℝ} (hab : a ≤ b) {N : ℕ} (hN : 0 < N)
    (i : Fin N) : cell a b N i ⊆ Icc a b := by
  intro t ht
  rw [← equal_cells_cover hab hN]
  exact mem_iUnion.mpr ⟨i, ht⟩

end CylinderCovering.RadialPartitionCover

end OAI
