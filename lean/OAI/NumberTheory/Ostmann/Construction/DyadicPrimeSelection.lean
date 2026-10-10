import OAI.NumberTheory.Ostmann.Preliminaries.PrimeReciprocalBound

namespace OAI

/-! # A prime block with retained logarithmic weight -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def dyadicPrimeBlock (P : Finset ℕ) (j : ℕ) : Finset ℕ :=
  P.filter fun p => Nat.log 2 p = j

theorem exists_dyadic_prime_block (P : Finset ℕ) (M : ℕ)
    (hM : ∀ p ∈ P, p ≤ M) (w : ℕ → ℝ) :
    ∃ j ≤ Nat.log 2 M, (∑ p ∈ P, w p) / (Nat.log 2 M + 1 : ℝ) ≤
      ∑ p ∈ dyadicPrimeBlock P j, w p := by
  let J := Finset.range (Nat.log 2 M + 1)
  have hJ : J.Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hsum : (∑ j ∈ J, ∑ p ∈ dyadicPrimeBlock P j, w p) = ∑ p ∈ P, w p := by
    exact Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hM p hp)))) w
  have hconst : (∑ _j ∈ J, (∑ p ∈ P, w p) / (Nat.log 2 M + 1 : ℝ)) = ∑ p ∈ P, w p := by
    simp only [J, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  obtain ⟨j, hj, hlarge⟩ := Finset.exists_le_of_sum_le hJ (hconst.trans hsum.symm).le
  exact ⟨j, Nat.le_of_lt_succ (Finset.mem_range.mp hj), hlarge⟩

theorem dyadicPrimeBlock_bounds (P : Finset ℕ) (j : ℕ)
    (hP : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p ∈ dyadicPrimeBlock P j) :
    2 ^ j ≤ p ∧ p < 2 * 2 ^ j := by
  obtain ⟨hpP, he⟩ := Finset.mem_filter.mp hp
  have hlo := Nat.pow_log_le_self 2 (hP p hpP).ne_zero
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
  rw [he] at hlo hhi
  rw [pow_succ] at hhi
  exact ⟨hlo, by omega⟩

theorem dyadicPrimeBlock_weight_le (P : Finset ℕ) (j : ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ dyadicPrimeBlock P j, Real.log (p : ℝ) / p) ≤
      (dyadicPrimeBlock P j).card * (Real.log (2 * (2 : ℝ) ^ j) / (2 : ℝ) ^ j) := by
  calc
    _ ≤ ∑ _p ∈ dyadicPrimeBlock P j, Real.log (2 * (2 : ℝ) ^ j) / (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro p hp
      have hb := dyadicPrimeBlock_bounds P j hP hp
      have hpp := hP p (Finset.mem_filter.mp hp).1
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hlo : (2 : ℝ) ^ j ≤ p := by exact_mod_cast hb.1
      have hhi : (p : ℝ) ≤ 2 * (2 : ℝ) ^ j := by exact_mod_cast hb.2.le
      calc
        Real.log (p : ℝ) / p ≤ Real.log (p : ℝ) / (2 : ℝ) ^ j :=
          div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by positivity) hlo
        _ ≤ _ := div_le_div_of_nonneg_right (Real.log_le_log hp0 hhi) (by positivity)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem exists_weighted_dyadic_prime_block (P : Finset ℕ) (M : ℕ) (W : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hM : ∀ p ∈ P, p ≤ M)
    (hW : 0 < W) (hmass : W ≤ ∑ p ∈ P, Real.log (p : ℝ) / p) :
    ∃ (Z : ℕ) (R : Finset ℕ), 1 ≤ Z ∧ R ⊆ P ∧ R.Nonempty ∧
      (∀ p ∈ R, Z ≤ p ∧ p < 2 * Z) ∧
      W * Z ≤ (Nat.log 2 M + 1 : ℝ) * Real.log (2 * (Z : ℝ)) * R.card := by
  obtain ⟨j, hj, hweight⟩ := exists_dyadic_prime_block P M hM (fun p => Real.log (p : ℝ) / p)
  let Z := 2 ^ j
  let R := dyadicPrimeBlock P j
  have hJ : (0 : ℝ) < Nat.log 2 M + 1 := by positivity
  have hweight' : W / (Nat.log 2 M + 1 : ℝ) ≤ ∑ p ∈ R, Real.log (p : ℝ) / p :=
    (div_le_div_of_nonneg_right hmass hJ.le).trans hweight
  have hR : R.Nonempty := by
    by_contra hn
    have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he, Finset.sum_empty] at hweight'
    exact (div_pos hW hJ).not_ge hweight'
  refine ⟨Z, R, one_le_pow₀ (by norm_num), Finset.filter_subset _ _, hR,
    fun p hp => dyadicPrimeBlock_bounds P j hP hp, ?_⟩
  have hb := hweight'.trans (dyadicPrimeBlock_weight_le P j hP)
  have hZ : (0 : ℝ) < Z := by dsimp [Z]; positivity
  have hZcast : (Z : ℝ) = (2 : ℝ) ^ j := by simp [Z]
  rw [← hZcast] at hb
  have hb' := (div_le_iff₀ hJ).mp hb
  have hb'' := mul_le_mul_of_nonneg_right hb' hZ.le
  convert hb'' using 1
  field_simp
  ring

end Ostmann

end OAI
