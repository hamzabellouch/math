import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset

namespace OrdinaryLogDifferencing

lemma energy_le_gram {ι : Type*} (P : Finset ι) (b : ι → ℕ → ℂ) (N : ℕ) :
    (∑n∈range N,‖∑p∈P,b p n‖^2) ≤
      ∑p∈P,∑q∈P,‖∑n∈range N,b p n*star (b q n)‖ := by
  have he : ((∑n∈range N,‖∑p∈P,b p n‖^2:ℝ):ℂ)=
      ∑p∈P,∑q∈P,∑n∈range N,b p n*star (b q n) := by
    simp only [Complex.ofReal_sum,Complex.ofReal_pow,←Complex.mul_conj',map_sum]
    simp_rw [sum_mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    rw [sum_comm]
    rfl
  calc
    _ = ‖((∑n∈range N,‖∑p∈P,b p n‖^2:ℝ):ℂ)‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
      exact sum_nonneg (fun n hn => sq_nonneg _)
    _ = _ := congrArg norm he
    _ ≤ ∑p∈P,‖∑q∈P,∑n∈range N,b p n*star (b q n)‖ := norm_sum_le _ _
    _ ≤ _ := sum_le_sum (fun p hp => norm_sum_le _ _)

lemma norm_sum_sq {ι : Type*} (S : Finset ι) (z : ι → ℂ) :
    ‖∑ n ∈ S, z n‖^2 ≤ (S.card : ℝ) * ∑ n ∈ S, ‖z n‖^2 := by
  calc
    _ ≤ (∑ n ∈ S, ‖z n‖)^2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ _ := sq_sum_le_card_mul_sum_sq

lemma shift_difference (z : ℕ → ℂ) (N h : ℕ) :
    (∑ n ∈ range N, z (n+h)) - ∑ n ∈ range N, z n =
      (∑ n ∈ range h, z (N+n)) - ∑ n ∈ range h, z n := by
  have h₁ := Finset.sum_range_add z h N
  have h₂ := Finset.sum_range_add z N h
  simp only [Nat.add_comm h N] at h₁
  simp only [Nat.add_comm h] at h₁
  linear_combination -h₁ + h₂

lemma norm_shift_difference (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) (N h : ℕ) :
    ‖(∑ n ∈ range N, z (n+h)) - ∑ n ∈ range N, z n‖ ≤ 2 * h := by
  rw [shift_difference]
  have hsum (f : ℕ → ℕ) : ‖∑ n ∈ range h, z (f n)‖ ≤ h := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ n ∈ range h, (1 : ℝ) := sum_le_sum (fun n hn => hz (f n))
      _ = _ := by simp
  have hh : ‖∑ n ∈ range h, z n‖ ≤ h := by simpa only [id_eq] using hsum id
  exact (norm_sub_le _ _).trans (by linarith [hsum (fun n => N+n)])

lemma shift_average_error (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) (N H : ℕ) :
    ‖(H : ℂ) * (∑ n ∈ range N, z n) -
      ∑ n ∈ range N, ∑ h ∈ range H, z (n+h)‖ ≤ 2 * (H : ℝ)^2 := by
  have he : (H : ℂ) * (∑ n ∈ range N, z n) -
      ∑ n ∈ range N, ∑ h ∈ range H, z (n+h) =
      ∑ h ∈ range H, ((∑ n ∈ range N, z n) - ∑ n ∈ range N, z (n+h)) := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, sum_comm]
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ h ∈ range H, 2 * (H : ℝ) := by
      apply sum_le_sum
      intro h hh
      rw [norm_sub_rev]
      exact (norm_shift_difference z hz N h).trans (by
        have : (h : ℝ) ≤ H := by exact_mod_cast (Nat.le_of_lt (mem_range.mp hh))
        linarith)
    _ = _ := by simp; ring

theorem finite_differencing (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) (N H : ℕ) :
    (H : ℝ)^2 * ‖∑ n ∈ range N, z n‖^2 ≤
      2 * N * (∑ h ∈ range H, ∑ k ∈ range H,
        ‖∑ n ∈ range N, z (n+h) * star (z (n+k))‖) + 8 * (H : ℝ)^4 := by
  let S := ∑ n ∈ range N, z n
  let V := ∑ n ∈ range N, ∑ h ∈ range H, z (n+h)
  have he := shift_average_error z hz N H
  change ‖(H : ℂ) * S - V‖ ≤ 2 * (H : ℝ)^2 at he
  have hnorm : (H : ℝ) * ‖S‖ ≤ ‖V‖ + 2 * (H : ℝ)^2 := by
    calc
      _ = ‖(H : ℂ) * S‖ := by simp
      _ ≤ ‖V‖ + ‖(H : ℂ) * S - V‖ := by
        have hh := norm_add_le V ((H : ℂ) * S - V)
        simpa only [add_sub_cancel] using hh
      _ ≤ _ := add_le_add le_rfl he
  have hsq : (H : ℝ)^2 * ‖S‖^2 ≤ 2 * ‖V‖^2 + 8 * (H : ℝ)^4 := by
    have hh := sq_le_sq₀ (by positivity : 0 ≤ (H : ℝ) * ‖S‖) (by positivity) |>.mpr hnorm
    nlinarith [sq_nonneg (‖V‖ - 2 * (H : ℝ)^2)]
  have hV : ‖V‖^2 ≤ (N : ℝ) *
      (∑ h ∈ range H, ∑ k ∈ range H, ‖∑ n ∈ range N, z (n+h) * star (z (n+k))‖) := by
    have hf : ‖V‖^2 ≤ (N : ℝ) * ∑ n ∈ range N, ‖∑ h ∈ range H, z (n+h)‖^2 := by
      simpa only [V, card_range] using norm_sum_sq (range N) (fun n => ∑ h ∈ range H, z (n+h))
    exact hf.trans (mul_le_mul_of_nonneg_left (energy_le_gram (range H) (fun h n => z (n+h)) N)
        (by positivity))
  change (H : ℝ)^2 * ‖S‖^2 ≤ _
  nlinarith

theorem row_gap_sum (H h : ℕ) (hh : h < H) (f : ℕ → ℝ)
    (hf : ∀ d, 0 ≤ f d) :
    (∑ k ∈ range H, if h = k then 0 else f (Nat.dist h k)) ≤
      2 * ∑ d ∈ Icc 1 H, f d := by
  have hlo : (∑ k ∈ (range H).filter (· < h), f (h-k)) ≤ ∑ d ∈ Icc 1 H, f d := by
    have hinj : Set.InjOn (fun k => h-k) ↑((range H).filter (· < h)) := by
      intro k hk l hl he
      have hk' := (mem_filter.mp hk).2
      have hl' := (mem_filter.mp hl).2
      dsimp at he
      omega
    rw [← sum_image hinj]
    apply sum_le_sum_of_subset_of_nonneg _ (fun d _ _ => hf d)
    intro d hd
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hd
    have hk' := (mem_filter.mp hk).2
    simp only [mem_Icc]
    omega
  have hhi : (∑ k ∈ (range H).filter (h < ·), f (k-h)) ≤ ∑ d ∈ Icc 1 H, f d := by
    have hinj : Set.InjOn (fun k => k-h) ↑((range H).filter (h < ·)) := by
      intro k hk l hl he
      have hk' := (mem_filter.mp hk).2
      have hl' := (mem_filter.mp hl).2
      dsimp at he
      omega
    rw [← sum_image hinj]
    apply sum_le_sum_of_subset_of_nonneg _ (fun d _ _ => hf d)
    intro d hd
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hd
    obtain ⟨hkH, hhk⟩ := mem_filter.mp hk
    have hk' := mem_range.mp hkH
    simp only [mem_Icc]
    omega
  have he : (∑ k ∈ range H, if h = k then 0 else f (Nat.dist h k)) =
      (∑ k ∈ (range H).filter (· < h), f (h-k)) +
        ∑ k ∈ (range H).filter (h < ·), f (k-h) := by
    rw [sum_filter, sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    rcases lt_trichotomy k h with hkh | hkh | hkh
    · simp only [ite_eq_left hkh, ite_eq_right (by omega : ¬h < k), add_zero,
        ite_eq_right (by omega : ¬h = k), Nat.dist_eq_sub_of_le_right hkh.le]
    · subst k
      simp
    · simp only [ite_eq_right (by omega : ¬k < h), ite_eq_left hkh, zero_add,
        ite_eq_right (by omega : ¬h = k), Nat.dist_eq_sub_of_le hkh.le]
  rw [he]
  linarith

theorem correlation_envelope (H : ℕ) (C : ℕ → ℕ → ℝ) (D : ℝ)
    (f : ℕ → ℝ) (hf : ∀ d, 0 ≤ f d)
    (hdiag : ∀ h < H, C h h ≤ D)
    (hoff : ∀ h < H, ∀ k < H, h ≠ k → C h k ≤ f (Nat.dist h k)) :
    (∑ h ∈ range H, ∑ k ∈ range H, C h k) ≤
      (H : ℝ) * D + 2 * H * ∑ d ∈ Icc 1 H, f d := by
  calc
    _ ≤ ∑ h ∈ range H, (D + 2 * ∑ d ∈ Icc 1 H, f d) := by
      apply sum_le_sum
      intro h hh
      have hh' := mem_range.mp hh
      calc
        _ ≤ ∑ k ∈ range H, (if h = k then D else f (Nat.dist h k)) := by
          apply sum_le_sum
          intro k hk
          split_ifs with he
          · subst k; exact hdiag h hh'
          · exact hoff h hh' k (mem_range.mp hk) he
        _ = D + ∑ k ∈ range H, if h = k then 0 else f (Nat.dist h k) := by
          have he : (fun k => if h = k then D else f (Nat.dist h k)) =
              (fun k => (if h = k then D else 0) + (if h = k then 0 else f (Nat.dist h k))) := by
            funext k; split_ifs <;> simp
          rw [he, sum_add_distrib]
          simp only [sum_ite_eq, mem_range, ite_eq_left hh']
        _ ≤ _ := add_le_add_right (row_gap_sum H h hh' f hf) D
    _ = _ := by simp; ring

end OrdinaryLogDifferencing

end

end OAI
