import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantBounds

namespace OAI

/-! # The regular product and separated arithmetic modulus share one cutoff -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The regular primes are included before absorbing the logarithmic budget.
This retains the slack between the nongiant and giant progression scales. -/
theorem movingArithmeticModuli_with_regular_giant_range (n : ℕ) (F K H : ℝ)
    (hF : 0 ≤ F) (hK : 0 ≤ K) (hH : 0 ≤ H) :
    ∀ᶠ L : ℝ in atTop, ∀ (m r : ℕ) (p : Fin m → ℕ) (P : Finset ℕ) (reg : ℕ),
      (m : ℝ) ≤ K * L → P.card ≤ 4 * n * 2 ^ n →
      (r : ℝ) ≤ Real.exp (F * m) →
      (∀ q ∈ P, (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (reg : ℝ) ≤ Real.exp (H * L * Real.exp ((11 / 1000 : ℝ) * L)) →
      reg * (∏ b, movingArithmeticModuli r p P Finset.univ b) ≤
        giantProgressionCutoff L := by
  let J : ℝ := 4 * n * 2 ^ n
  let C := F * K + 2 * J + K + H
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hFK : 0 ≤ F * K := mul_nonneg hF hK
  filter_upwards [arithmetic_exponent_absorption (11 / 1000) (12 / 1000) 0 C 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro m r p P reg hm hc hr hP hp hreg
  apply Nat.le_floor
  have hbound := movingArithmeticModuli_exp_bound m r p P F
    (Real.exp ((11 / 1000 : ℝ) * L)) (Real.exp ((1 / 1000 : ℝ) * L)) hr hP hp
  have htotal : ((reg * ∏ b, movingArithmeticModuli r p P Finset.univ b : ℕ) : ℝ) ≤
      Real.exp (F * m + 2 * P.card * Real.exp ((11 / 1000 : ℝ) * L) +
        (m : ℝ) * Real.exp ((1 / 1000 : ℝ) * L) + H * L * Real.exp ((11 / 1000 : ℝ) * L)) := by
    rw [Nat.cast_mul]
    apply (mul_le_mul hreg hbound (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add]
    congr 1
    ring
  apply htotal.trans
  change Real.exp _ ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * (10 * L)))
  rw [show (12 / 10000 : ℝ) * (10 * L) = (12 / 1000 : ℝ) * L by ring]
  apply Real.exp_le_exp.mpr
  have hc' : (P.card : ℝ) ≤ J := by
    dsimp only [J]
    exact_mod_cast hc
  have he : Real.exp ((1 / 1000 : ℝ) * L) ≤ Real.exp ((11 / 1000 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by linarith)
  have hKL : 0 ≤ K * L := mul_nonneg hK (by linarith)
  have hmain := mul_le_mul_of_nonneg_left hm hF
  have hi := mul_le_mul_of_nonneg_right hc' (Real.exp_nonneg ((11 / 1000 : ℝ) * L))
  have hiL : 2 * J * Real.exp ((11 / 1000 : ℝ) * L) ≤
      (2 * J * L) * Real.exp ((11 / 1000 : ℝ) * L) := by
    exact mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (mul_nonneg (by norm_num) hJ) hL) (Real.exp_nonneg _)
  have hs := mul_le_mul hm he (Real.exp_nonneg _) hKL
  have hC1 : F * K ≤ C := by dsimp only [C]; linarith
  have hC2 : 2 * J + K + H ≤ C := by dsimp only [C]; linarith
  have hC1L := mul_le_mul_of_nonneg_right hC1 (show 0 ≤ L by linarith)
  have hC2L := mul_le_mul_of_nonneg_right hC2 (show 0 ≤ L by linarith)
  have hC2e := mul_le_mul_of_nonneg_right hC2L (Real.exp_nonneg ((11 / 1000 : ℝ) * L))
  simp only [pow_one, zero_mul, Real.exp_zero, one_mul] at hrate
  nlinarith only [hmain, hi, hiL, hs, hC1L, hC2e, hrate]

theorem movingPattern_regular_exp_range (n r₀ k : ℕ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (B C : Type) (N : ℕ) (e : Fin (N + 1) ≃ B ⊕ C)
        (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
        (value : Fin (N + 1) → ℕ),
      MovingLeafLengthLE n small r₀ →
      (∀ i, (value i : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
          flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))) : ℝ) ≤
        Real.exp (((2 ^ n : ℕ) : ℝ) * ((r₀ : ℝ) + (k : ℝ) ^ 4) * L *
          Real.exp ((11 / 1000 : ℝ) * L)) := by
  let K : ℝ := (2 ^ n : ℕ) * ((r₀ : ℝ) + (k : ℝ) ^ 4)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hlarge
  dsimp only
  intro B C N e small slot value hsmall hvalue
  apply (naturalProduct_exp_bound value (Real.exp ((11 / 1000 : ℝ) * L)) hvalue _).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  have hsmall' := moving_flatten_length_le n (movingPatternFiniteSmall e n small) r₀
    (movingLeafLengthLE_map _ n small r₀ hsmall)
  have hbulk := moving_flatten_length_le n
    (bulkSlotLeaves n (spectatorBulkCount k L) (movingPatternBulkEmbedding e slot))
    (spectatorBulkCount k L) (bulkSlotLeaves_length n _ _)
  have hlen := Nat.cast_le (α := ℝ).mpr (Nat.add_le_add hsmall' hbulk)
  have hm := spectatorBulkCount_upper k L (by linarith)
  have hr := mul_le_mul_of_nonneg_left hlarge (Nat.cast_nonneg r₀)
  have hh := mul_le_mul_of_nonneg_left (add_le_add hr hm)
    (show (0 : ℝ) ≤ (2 ^ n : ℕ) by positivity)
  rw [List.length_append, Nat.cast_add]
  push_cast at hlen
  apply hlen.trans
  simpa only [K, mul_one, Nat.cast_pow, Nat.cast_ofNat, mul_add, add_mul, mul_assoc] using hh

/-- The actual frequency tree, internal image and regular product fit the
same giant cutoff, rather than two separately exhausted budgets. -/
theorem movingPattern_actual_separated_modulus_range (n r₀ k : ℕ)
    (Cfreq : ℝ) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (B C : Type) (N : ℕ) (e : Fin (N + 1) ≃ B ⊕ C)
        (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
        (value : Fin (N + 1) → ℕ)
        (S : Finset ℤ) (Nfreq : ℕ) (t : FrequencyTree (S × S) n)
        (p : Fin m → ℕ) (P : Finset ℕ),
      MovingLeafLengthLE n small r₀ →
      (∀ i, (value i : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ Nfreq) →
      (Nfreq : ℝ) ≤ Real.exp (Cfreq * m) → P.card ≤ 4 * n * 2 ^ n →
      (∀ q ∈ P, q.Prime ∧ (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, (p i).Prime ∧ (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      let reg := MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
          flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot)))
      let M := ∏ b, movingArithmeticModuli (frequencyModelBase S n t ^ (n - 1 + 2))
        p P Finset.univ b
      reg * M ≤ giantProgressionCutoff L := by
  let D : ℕ := 2 * (2 ^ (n + 1) - 1) * (n - 1 + 2)
  let H : ℝ := (2 ^ n : ℕ) * ((r₀ : ℝ) + (k : ℝ) ^ 4)
  filter_upwards [movingArithmeticModuli_with_regular_giant_range n
      ((D : ℝ) * Cfreq) ((k : ℝ) ^ 4) H
      (by positivity) (by positivity) (by dsimp only [H]; positivity),
    movingPattern_regular_exp_range n r₀ k, eventually_ge_atTop (0 : ℝ)]
    with L hL hregular hL0
  dsimp only at hregular ⊢
  intro B C N e small slot value S Nfreq t p P hsmall hvalue hS hN hcard hP hp
  let r := frequencyModelBase S n t ^ (n - 1 + 2)
  have hr : (r : ℝ) ≤ Real.exp (((D : ℝ) * Cfreq) * spectatorBulkCount k L) := by
    simpa only [mul_assoc, D, r] using frequencyModelModulus_exp_bound S Nfreq n t
      (Cfreq * spectatorBulkCount k L) (fun s hs => (hS s hs).2) hN
  exact hL (spectatorBulkCount k L) r p P _ (spectatorBulkCount_upper k L hL0)
    hcard hr (fun q hq => (hP q hq).2) (fun i => (hp i).2)
    (hregular B C N e small slot value hsmall hvalue)

end Ostmann

end OAI
