import OAI.NumberTheory.ShortEgyptian.WindowDiscrepancy

namespace OAI

universe uα

namespace ShortEgyptian

open scoped BigOperators
open Finset

noncomputable def empiricalMass {α : Type uα} [Fintype α] {q : ℕ} [NeZero q]
    (v : α → ZMod q) (x : ZMod q) : ℝ :=
  ∑ i, if v i = x then (1 : ℝ) / Fintype.card α else 0

theorem empiricalMass_nonneg {α : Type uα} [Fintype α] {q : ℕ} [NeZero q]
    (v : α → ZMod q) (x : ZMod q) : 0 ≤ empiricalMass v x := by
  unfold empiricalMass
  positivity

theorem empiricalMass_total {α : Type uα} [Fintype α] [Nonempty α]
    {q : ℕ} [NeZero q] (v : α → ZMod q) : ∑ x, empiricalMass v x = 1 := by
  unfold empiricalMass
  rw [Finset.sum_comm]
  simp [Fintype.card_ne_zero]

theorem empiricalMass_window {α : Type uα} [Fintype α] {q : ℕ} [NeZero q]
    (v : α → ZMod q) (I : Finset (ZMod q)) :
    ∑ x ∈ I, empiricalMass v x = ((Finset.univ.filter fun i => v i ∈ I).card : ℝ) / Fintype.card α := by
  classical
  unfold empiricalMass
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

noncomputable def indexedCharAverage {α : Type uα} [Fintype α] {q : ℕ} [NeZero q]
    (v : α → ZMod q) (k : ZMod q) : ℂ :=
  (∑ i, ZMod.stdAddChar (k * v i)) / Fintype.card α

theorem empiricalMass_fourier {α : Type uα} [Fintype α] {q : ℕ} [NeZero q]
    (v : α → ZMod q) (k : ZMod q) :
    probabilityFourier (empiricalMass (fun i => -v i)) k = indexedCharAverage v k := by
  classical
  unfold probabilityFourier empiricalMass indexedCharAverage
  push_cast
  simp only [apply_ite, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast, Complex.ofReal_zero]
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_neg, neg_neg, one_div]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

theorem indexedCharAverage_neg {α : Type uα} [Fintype α] {q : ℕ} [NeZero q]
    (v : α → ZMod q) (k : ZMod q) :
    indexedCharAverage v (-k) = (starRingEnd ℂ) (indexedCharAverage v k) := by
  unfold indexedCharAverage
  simp only [neg_mul, map_div₀, map_sum, map_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [AddChar.map_neg_eq_conj]

theorem indexed_residue_discrepancy {α : Type uα} [Fintype α] [Nonempty α]
    {q : ℕ} [NeZero q] (v : α → ZMod q) (δ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 256) (H : ℕ) (hH : 1 ≤ H)
    (hHδ : 1 ≤ 2 * (H : ℝ) * δ ^ 4)
    (hFourier : ∀ l : ℕ, 1 ≤ l → l ≤ H →
      ‖indexedCharAverage v (l : ZMod q)‖ ≤ δ ^ 3) :
    δ * Fintype.card α / 2 ≤ ((Finset.univ.filter fun i => ((-v i).val : ℝ) < δ * q).card : ℝ) := by
  classical
  have hkbound (k : ZMod q) (hk : k ≠ 0) (hd : frequencyDistance k ≤ H) :
      ‖probabilityFourier (empiricalMass (fun i => -v i)) k‖ ≤ δ ^ 3 := by
    rw [empiricalMass_fourier]
    have hkv : 0 < k.val := Nat.pos_of_ne_zero (fun hh => hk ((ZMod.val_eq_zero k).mp hh))
    dsimp [frequencyDistance] at hd
    rcases le_total k.val (q - k.val) with hmin | hmin
    · rw [min_eq_left hmin] at hd
      simpa only [ZMod.natCast_zmod_val] using hFourier k.val hkv hd
    · rw [min_eq_right hmin] at hd
      have hn : 1 ≤ q - k.val := by have hh := ZMod.val_lt k; omega
      have heq : ((q - k.val : ℕ) : ZMod q) = -k := by
        rw [Nat.cast_sub (ZMod.val_lt k).le]
        simp
      have hh := hFourier (q - k.val) hn hd
      rw [heq, indexedCharAverage_neg, Complex.norm_conj] at hh
      exact hh
  have hh := finite_residue_discrepancy δ hδ hδsmall H hH hHδ
    (empiricalMass (fun i => -v i)) (empiricalMass_nonneg _)
    (empiricalMass_total _) hkbound
  rw [empiricalMass_window] at hh
  have heq : (Finset.univ.filter fun i => -v i ∈ residueWindow q δ) =
      (Finset.univ.filter fun i => ((-v i).val : ℝ) < δ * q) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_residueWindow (by linarith : δ ≤ 1)]
  rw [heq] at hh
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have ht := (le_div_iff₀ hN).mp hh
  linarith

end ShortEgyptian

end OAI
