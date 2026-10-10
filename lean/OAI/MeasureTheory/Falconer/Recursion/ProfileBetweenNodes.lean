import OAI.MeasureTheory.Falconer.Recursion.ProfileNodeValues

namespace OAI

/-! Propagating the discrete profile bounds across each actual interpolation block. -/
namespace Falconer.Regularization

theorem finiteRampProfile_affine_on_block (d c : ℕ → ℝ) {K i : ℕ}
    (hd : Antitone d) (hi : i < K) {u : ℝ} (hu : d (i+1) ≤ u ∧ u ≤ d i) :
    finiteRampProfile d c K u = finiteRampProfile d c K (d (i+1))+c i*(u-d (i+1)) := by
  classical
  have hr (j : ℕ) : intervalRamp (d (j+1)) (d j) u-
      intervalRamp (d (j+1)) (d j) (d (i+1)) =
      if j = i then u-d (i+1) else 0 := by
    unfold intervalRamp
    by_cases hj : j = i
    · subst j
      rw [ite_eq_left rfl,min_eq_left hu.2,min_eq_right hu.1,
        min_eq_left (hd (Nat.le_succ i)),min_self]
      ring
    · rw [ite_eq_right hj]
      rcases lt_or_gt_of_ne hj with hj | hj
      · have h1 := hu.2.trans (hd (Nat.succ_le_of_lt hj))
        have h2 := hu.2.trans (hd (Nat.le_of_lt hj))
        have h3 := hd (show j+1 ≤ i+1 by omega)
        have h4 := hd (show j ≤ i+1 by omega)
        rw [min_eq_left h2,min_eq_left h1,min_eq_left h4,min_eq_left h3]
        ring
      · have h1 := (hd (show i+1 ≤ j by omega)).trans hu.1
        have h2 := (hd (show i+1 ≤ j+1 by omega)).trans hu.1
        have h3 := hd (show i+1 ≤ j by omega)
        have h4 := hd (show i+1 ≤ j+1 by omega)
        rw [min_eq_right h1,min_eq_right h2,min_eq_right h3,min_eq_right h4]
        ring
  have he : finiteRampProfile d c K u-finiteRampProfile d c K (d (i+1)) =
      ∑ j ∈ Finset.range K, c j*(intervalRamp (d (j+1)) (d j) u-
        intervalRamp (d (j+1)) (d j) (d (i+1))) := by
    simp only [finiteRampProfile,← Finset.sum_sub_distrib,mul_sub]
  simp_rw [hr] at he
  rw [Finset.sum_eq_single i (fun j _ hji => by simp [hji])
    (fun hni => False.elim (hni (Finset.mem_range.mpr hi)))] at he
  simp only [ite_true] at he
  linarith

theorem exists_profile_block (d : ℕ → ℝ) (_hd : Antitone d) (K : ℕ) {u : ℝ}
    (hu : d K ≤ u ∧ u ≤ d 0) :
    u = d 0 ∨ ∃ i < K, d (i+1) ≤ u ∧ u ≤ d i := by
  induction K with
  | zero => exact Or.inl (le_antisymm hu.2 hu.1)
  | succ K ih =>
    by_cases hlast : u ≤ d K
    · exact Or.inr ⟨K,Nat.lt_succ_self K,hu.1,hlast⟩
    · rcases ih ⟨(le_of_not_ge hlast),hu.2⟩ with he | ⟨i,hi,hui⟩
      · exact Or.inl he
      · exact Or.inr ⟨i,Nat.lt_succ_of_lt hi,hui⟩

theorem finiteRampProfile_lower_between_nodes (d c : ℕ → ℝ) (K : ℕ)
    (hd : Antitone d) {t A u : ℝ}
    (hnodes : ∀ i ≤ K, t*d i-A ≤ finiteRampProfile d c K (d i))
    (hu : d K ≤ u ∧ u ≤ d 0) : t*u-A ≤ finiteRampProfile d c K u := by
  rcases exists_profile_block d hd K hu with rfl | ⟨i,hi,hui⟩
  · exact hnodes 0 (Nat.zero_le _)
  · have hlow := hnodes (i+1) hi
    have hhigh := hnodes i hi.le
    have hf := finiteRampProfile_affine_on_block d c hd hi hui
    by_cases hs : t ≤ c i
    · have hm := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hui.1)
      nlinarith
    · have hf' := finiteRampProfile_affine_on_block d c hd hi
        (show d (i+1) ≤ d i ∧ d i ≤ d i from ⟨hd (Nat.le_succ i),le_rfl⟩)
      have hm := mul_nonneg (sub_nonneg.mpr (le_of_not_ge hs)) (sub_nonneg.mpr hui.2)
      nlinarith

end Falconer.Regularization

end OAI
