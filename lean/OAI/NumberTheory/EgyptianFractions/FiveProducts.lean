import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.FiveProducts

theorem character_map_sum {p : ℕ} [NeZero p] {ι : Type*}
    (s : Finset ι) (g : ι → ZMod p) :
    ZMod.stdAddChar (∑ i ∈ s, g i) = ∏ i ∈ s, ZMod.stdAddChar (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, AddChar.map_add_eq_mul, ih]

/-- Orthogonality for the standard character on a finite cyclic group. -/
theorem character_sum {p : ℕ} [NeZero p] (t : ZMod p) :
    (∑ r : ZMod p, ZMod.stdAddChar (t * r)) =
      if t = 0 then (p : ℂ) else 0 := by
  split_ifs with ht
  · simp [ht]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p ht)

/-- The character moment vanishes if no tuple has zero sum. -/
theorem moment_eq_zero_of_no_zero_sum {p : ℕ} [NeZero p]
    {X : Type*} [Fintype X] (f : X → ZMod p) (n : ℕ)
    (h : ∀ v : Fin n → X, ∑ i, f (v i) ≠ 0) :
    (∑ r : ZMod p, (∑ x : X, ZMod.stdAddChar (f x * r)) ^ n) = 0 := by
  classical
  simp_rw [Fintype.sum_pow]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro v hv
  have heq (r : ZMod p) :
      (∏ i : Fin n, ZMod.stdAddChar (f (v i) * r)) =
        ZMod.stdAddChar ((∑ i : Fin n, f (v i)) * r) := by
    rw [Finset.sum_mul]
    exact (character_map_sum Finset.univ _).symm
  simp_rw [heq]
  rw [character_sum, ite_eq_right (h v)]

/-- A strict spectral bound forces a zero-sum tuple. The estimate uses `p`
rather than `p-1`, which is convenient and sufficient for five products. -/
theorem exists_zero_sum_of_character_bound {p : ℕ} [NeZero p]
    {X : Type*} [Fintype X] (f : X → ZMod p) (n : ℕ) (B : ℝ)
    (hB : 0 ≤ B)
    (hchar : ∀ r : ZMod p, r ≠ 0 →
      ‖∑ x : X, ZMod.stdAddChar (f x * r)‖ ≤ B)
    (hsize : (p : ℝ) * B ^ n < (Fintype.card X : ℝ) ^ n) :
    ∃ v : Fin n → X, ∑ i, f (v i) = 0 := by
  classical
  by_contra h
  push Not at h
  let S : ZMod p → ℂ := fun r => (∑ x : X, ZMod.stdAddChar (f x * r)) ^ n
  have hz : ∑ r, S r = 0 := moment_eq_zero_of_no_zero_sum f n h
  have hs0 : S 0 = (Fintype.card X : ℂ) ^ n := by simp [S]
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (ZMod p)))
    S (Finset.mem_univ 0)
  rw [hz, hs0] at hsplit
  have heq : (Fintype.card X : ℝ) ^ n =
      ‖∑ r ∈ (Finset.univ : Finset (ZMod p)).erase 0, S r‖ := by
    have heqC : (Fintype.card X : ℂ) ^ n =
        -(∑ r ∈ (Finset.univ : Finset (ZMod p)).erase 0, S r) := by
      linear_combination hsplit
    have hn := congrArg norm heqC
    simpa only [norm_pow, Complex.norm_natCast, norm_neg] using hn
  have hle : ‖∑ r ∈ (Finset.univ : Finset (ZMod p)).erase 0, S r‖ ≤
      (p : ℝ) * B ^ n := by
    calc
      _ ≤ ∑ r ∈ (Finset.univ : Finset (ZMod p)).erase 0, ‖S r‖ := norm_sum_le _ _
      _ ≤ ∑ r ∈ (Finset.univ : Finset (ZMod p)).erase 0, B ^ n := by
        apply Finset.sum_le_sum
        intro r hr
        dsimp [S]
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hchar r (Finset.mem_erase.mp hr).1) n
      _ ≤ ∑ r : ZMod p, B ^ n := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => pow_nonneg hB n)
      _ = (p : ℝ) * B ^ n := by simp
  linarith

/-- Parseval for the standard character restricted to a set. -/
theorem character_parseval {p : ℕ} [Fact p.Prime] (H : Finset (ZMod p))
    (r : ZMod p) (hr : r ≠ 0) :
    (∑ a : ZMod p, ‖∑ b ∈ H, ZMod.stdAddChar (b * a * r)‖ ^ 2) =
      (p : ℝ) * H.card := by
  classical
  have heq (a b c : ZMod p) :
      ZMod.stdAddChar (b * a * r) *
          (starRingEnd ℂ) (ZMod.stdAddChar (c * a * r)) =
        ZMod.stdAddChar (((b - c) * r) * a) := by
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hc : (∑ a : ZMod p,
      (∑ b ∈ H, ZMod.stdAddChar (b * a * r)) *
        (starRingEnd ℂ) (∑ c ∈ H, ZMod.stdAddChar (c * a * r))) =
      (p : ℂ) * H.card := by
    simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum, heq]
    rw [Finset.sum_comm]
    calc
      _ = ∑ b ∈ H, ∑ c ∈ H,
          ∑ a : ZMod p, ZMod.stdAddChar (((b - c) * r) * a) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.sum_comm]
      _ = ∑ b ∈ H, ∑ c ∈ H, if b = c then (p : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        rw [character_sum]
        simp [hr, sub_eq_zero]
      _ = (p : ℂ) * H.card := by simp [mul_comm]
  simp_rw [Complex.mul_conj'] at hc
  exact_mod_cast hc

/-- The finite-field bilinear character bound, in unnormalised form. -/
theorem bilinear_character_bound {p : ℕ} [Fact p.Prime]
    (H : Finset (ZMod p)) (r : ZMod p) (hr : r ≠ 0) :
    ‖∑ a ∈ H, ∑ b ∈ H, ZMod.stdAddChar (b * a * r)‖ ≤
      Real.sqrt p * H.card := by
  classical
  let S : ZMod p → ℂ := fun a => ∑ b ∈ H, ZMod.stdAddChar (b * a * r)
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq H
    (fun _ : ZMod p => (1 : ℝ)) (fun a => ‖S a‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcauchy
  have htriangle : ‖∑ a ∈ H, S a‖ ≤ ∑ a ∈ H, ‖S a‖ := norm_sum_le _ _
  have hnonneg : 0 ≤ ∑ a ∈ H, ‖S a‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsquare : ‖∑ a ∈ H, S a‖ ^ 2 ≤
      (H.card : ℝ) * ∑ a ∈ H, ‖S a‖ ^ 2 := by
    nlinarith [norm_nonneg (∑ a ∈ H, S a)]
  have hsubset : (∑ a ∈ H, ‖S a‖ ^ 2) ≤ ∑ a : ZMod p, ‖S a‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
      (fun _ _ _ => sq_nonneg _)
  have hparseval : (∑ a : ZMod p, ‖S a‖ ^ 2) = (p : ℝ) * H.card :=
    character_parseval H r hr
  have hmul := mul_le_mul_of_nonneg_left hsubset (Nat.cast_nonneg H.card : (0 : ℝ) ≤ H.card)
  rw [hparseval] at hmul
  have hsqrt : (Real.sqrt (p : ℝ)) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have htarget : 0 ≤ Real.sqrt (p : ℝ) * H.card := by positivity
  change ‖∑ a ∈ H, S a‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) htarget).mp
  calc
    _ ≤ (H.card : ℝ) * ((p : ℝ) * H.card) := hsquare.trans hmul
    _ = (Real.sqrt (p : ℝ) * H.card) ^ 2 := by
      rw [mul_pow, hsqrt]
      ring

/-- Five products from a sufficiently large set in a prime field have sum zero.
The integral threshold is slightly stronger than the optimal Fourier threshold
only in its strictness, and is implied by `|H| > p^(3/4)`. -/
theorem five_products_zero_of_power_bound {p : ℕ} [Fact p.Prime]
    (H : Finset (ZMod p)) (hsize : p ^ 7 < H.card ^ 10) :
    ∃ a b : Fin 5 → H, ∑ i, (a i : ZMod p) * (b i : ZMod p) = 0 := by
  classical
  have hsizeR : (p : ℝ) ^ 7 < (H.card : ℝ) ^ 10 := by exact_mod_cast hsize
  have hh : 0 < (H.card : ℝ) ^ 10 := lt_of_le_of_lt (by positivity) hsizeR
  have hsqrt : (Real.sqrt (p : ℝ)) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have hspectral : (p : ℝ) * (Real.sqrt p * H.card) ^ 5 <
      (Fintype.card (H × H) : ℝ) ^ 5 := by
    simp only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul]
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    calc
      ((p : ℝ) * (Real.sqrt p * H.card) ^ 5) ^ 2 =
          (p : ℝ) ^ 2 * ((Real.sqrt p) ^ 2) ^ 5 * (H.card : ℝ) ^ 10 := by ring
      _ = (p : ℝ) ^ 7 * (H.card : ℝ) ^ 10 := by rw [hsqrt]; ring
      _ < (H.card : ℝ) ^ 10 * (H.card : ℝ) ^ 10 := mul_lt_mul_of_pos_right hsizeR hh
      _ = (((H.card : ℝ) * H.card) ^ 5) ^ 2 := by ring
  have hchar (r : ZMod p) (hr : r ≠ 0) :
      ‖∑ z : H × H, ZMod.stdAddChar (((z.2 : ZMod p) * (z.1 : ZMod p)) * r)‖ ≤
        Real.sqrt p * H.card := by
    rw [Fintype.sum_prod_type]
    have hi (a : ZMod p) :
        (∑ b : H, ZMod.stdAddChar ((b : ZMod p) * a * r)) =
          ∑ b ∈ H, ZMod.stdAddChar (b * a * r) := Finset.sum_coe_sort H (fun b : ZMod p => ZMod.stdAddChar (b * a * r))
    simp_rw [hi]
    rw [Finset.sum_coe_sort H (fun a => ∑ b ∈ H, ZMod.stdAddChar (b * a * r))]
    exact bilinear_character_bound H r hr
  obtain ⟨v, hv⟩ := exists_zero_sum_of_character_bound
    (fun z : H × H => (z.2 : ZMod p) * (z.1 : ZMod p)) 5
    (Real.sqrt p * H.card) (by positivity) hchar hspectral
  exact ⟨fun i => (v i).2, fun i => (v i).1, hv⟩

/-- The five-product conclusion at the `p^(3/4)` threshold used in
rational-divisor supply. -/
theorem five_products_zero {p : ℕ} [Fact p.Prime]
    (H : Finset (ZMod p)) (hsize : (p : ℝ) ^ (3 / 4 : ℝ) < H.card) :
    ∃ a b : Fin 5 → H, ∑ i, (a i : ZMod p) * (b i : ZMod p) = 0 := by
  apply five_products_zero_of_power_bound H
  have hp : (1 : ℝ) ≤ p := by
    exact_mod_cast (Nat.Prime.one_lt (Fact.out : Nat.Prime p)).le
  have hpow := Real.rpow_lt_rpow (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    hsize (by norm_num : (0 : ℝ) < 10)
  rw [← Real.rpow_mul (Nat.cast_nonneg p)] at hpow
  have hmon : (p : ℝ) ^ (7 : ℝ) ≤ (p : ℝ) ^ ((3 / 4 : ℝ) * 10) :=
    Real.rpow_le_rpow_of_exponent_le hp (by norm_num)
  have hh : (p : ℝ) ^ (7 : ℝ) < (H.card : ℝ) ^ (10 : ℝ) := hmon.trans_lt hpow
  norm_cast at hh

end Problem337.FiveProducts

end

end OAI
