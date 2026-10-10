import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternModulusRange
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkBudgets
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # Concrete logarithmic bounds for the original giant comparison -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem giantProgressionCutoff_log_le {M : ℕ} {L : ℝ}
    (hM : 0 < M) (hbound : M ≤ giantProgressionCutoff L) :
    Real.log (M : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) := by
  have hupper : (M : ℝ) ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) := by
    apply (Nat.cast_le.mpr hbound).trans
    have h := Nat.floor_le (Real.exp_nonneg (Real.exp ((12 / 10000 : ℝ) * (10 * L))))
    simpa only [giantProgressionCutoff, bulkProgressionCutoff,
      show (12 / 10000 : ℝ) * (10 * L) = (12 / 1000 : ℝ) * L by ring] using h
  have hlog := Real.log_le_log (show (0 : ℝ) < M by exact_mod_cast hM) hupper
  simpa only [Real.log_exp] using hlog

theorem naturalProduct_exp_bound {σ : Type*} (value : σ → ℕ) (A : ℝ)
    (hvalue : ∀ i, (value i : ℝ) ≤ Real.exp A) (slots : List σ) :
    (MovingSlotReversal.naturalProduct value slots : ℝ) ≤ Real.exp (slots.length * A) := by
  induction slots with
  | nil => simp [MovingSlotReversal.naturalProduct]
  | cons i slots ih =>
    simp only [MovingSlotReversal.naturalProduct, List.map_cons, List.prod_cons, Nat.cast_mul]
    apply (mul_le_mul (hvalue i) ih (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add, List.length_cons, Nat.cast_add, Nat.cast_one]
    congr 1
    ring

theorem naturalProduct_log_bound {σ : Type*} (value : σ → ℕ) (A : ℝ)
    (hpos : ∀ i, value i ≠ 0) (hvalue : ∀ i, (value i : ℝ) ≤ Real.exp A) (slots : List σ) :
    Real.log (MovingSlotReversal.naturalProduct value slots : ℝ) ≤ slots.length * A := by
  have hn : MovingSlotReversal.naturalProduct value slots ≠ 0 := by
    apply List.prod_ne_zero
    intro hz
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hz
    exact hpos i hi
  have hp : (0 : ℝ) < MovingSlotReversal.naturalProduct value slots := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have h := Real.log_le_log hp (naturalProduct_exp_bound value A hvalue slots)
  simpa only [Real.log_exp] using h

/-- A list containing linearly many primes in the actual nongiant range
satisfies the logarithmic budget used by the giant progression theorem. -/
theorem naturalProduct_giant_log_range (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type) (value : σ → ℕ) (slots : List σ),
      (∀ i, value i ≠ 0) → (slots.length : ℝ) ≤ K * L →
      (∀ i, (value i : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      Real.log (MovingSlotReversal.naturalProduct value slots : ℝ) ≤
        Real.exp ((12 / 1000 : ℝ) * L) := by
  filter_upwards [arithmetic_exponent_absorption (11 / 1000) (12 / 1000) 0 K 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)] with L hL
  intro σ value slots hpos hlen hvalue
  have hlog := naturalProduct_log_bound value (Real.exp ((11 / 1000 : ℝ) * L)) hpos hvalue slots
  have hlen' := mul_le_mul_of_nonneg_right hlen (Real.exp_nonneg ((11 / 1000 : ℝ) * L))
  simp only [pow_zero, mul_one, zero_mul, Real.exp_zero, one_mul] at hL
  exact (hlog.trans hlen').trans (by linarith)

/-- The common regular product of both histories uses only the original
small and bulk leaves. Its logarithmic budget follows from their lengths. -/
theorem movingPattern_regular_giant_log_range (n r₀ k : ℕ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (B C : Type) (N : ℕ) (e : Fin (N + 1) ≃ B ⊕ C)
        (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
        (value : Fin (N + 1) → ℕ),
      MovingLeafLengthLE n small r₀ → (∀ i, value i ≠ 0) →
      (∀ i, (value i : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      Real.log (MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n (movingPatternFiniteSmall e n small) ++
          flattenMovingSlots n (bulkSlotLeaves n m (movingPatternBulkEmbedding e slot))) : ℝ) ≤
        Real.exp ((12 / 1000 : ℝ) * L) := by
  let K : ℝ := (2 ^ n : ℕ) * ((r₀ : ℝ) + (k : ℝ) ^ 4)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  filter_upwards [naturalProduct_giant_log_range K hK, eventually_ge_atTop (1 : ℝ)]
    with L hL hlarge
  dsimp only
  intro B C N e small slot value hsmall hpos hvalue
  apply hL (Fin (N + 1)) value _ hpos _ hvalue
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

/-- The frequency modulus used by the actual pair of histories has a fixed
polynomial degree in the frequency cutoff. -/
theorem frequencyModelModulus_exp_bound (S : Finset ℤ) (N n : ℕ)
    (t : FrequencyTree (S × S) n) (A : ℝ)
    (hN : ∀ s ∈ S, s.natAbs ≤ N) (hA : (N : ℝ) ≤ Real.exp A) :
    ((frequencyModelBase S n t ^ (n - 1 + 2) : ℕ) : ℝ) ≤
      Real.exp ((2 * (2 ^ (n + 1) - 1) * (n - 1 + 2) : ℕ) * A) := by
  calc
    _ ≤ (N : ℝ) ^ (2 * (2 ^ (n + 1) - 1) * (n - 1 + 2)) := by
      exact_mod_cast frequencyModelModulus_bound S N n hN t
    _ ≤ (Real.exp A) ^ (2 * (2 ^ (n + 1) - 1) * (n - 1 + 2)) :=
      pow_le_pow_left₀ (Nat.cast_nonneg N) hA _
    _ = _ := (Real.exp_nat_mul _ _).symm

/-- The paired frequency modulus, the actual internal prime image, and the
selected spectators all fit the giant cutoff at the manuscript scales. -/
theorem movingPattern_actual_modulus_range (n k : ℕ) (Cfreq : ℝ) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (S : Finset ℤ) (N : ℕ) (t : FrequencyTree (S × S) n)
        (p : Fin m → ℕ) (P : Finset ℕ),
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) → (N : ℝ) ≤ Real.exp (Cfreq * m) →
      P.card ≤ 4 * n * 2 ^ n →
      (∀ q ∈ P, q.Prime ∧ (q : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, (p i).Prime ∧ (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      let M := ∏ b, movingArithmeticModuli (frequencyModelBase S n t ^ (n - 1 + 2))
        p P Finset.univ b
      M ≤ giantProgressionCutoff L ∧ Real.log (M : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) := by
  let D : ℕ := 2 * (2 ^ (n + 1) - 1) * (n - 1 + 2)
  filter_upwards [movingArithmeticModuli_giant_range n ((D : ℝ) * Cfreq) ((k : ℝ) ^ 4)
      (by positivity) (by positivity), eventually_ge_atTop (0 : ℝ)] with L hL hL0
  dsimp only
  intro S N t p P hS hN hcard hP hp
  let r := frequencyModelBase S n t ^ (n - 1 + 2)
  have hr : (r : ℝ) ≤ Real.exp (((D : ℝ) * Cfreq) * spectatorBulkCount k L) := by
    simpa only [mul_assoc, D, r] using frequencyModelModulus_exp_bound S N n t
      (Cfreq * spectatorBulkCount k L) (fun s hs => (hS s hs).2) hN
  have hbound := hL (spectatorBulkCount k L) r p P (spectatorBulkCount_upper k L hL0)
    hcard hr (fun q hq => (hP q hq).2) (fun i => (hp i).2)
  refine ⟨hbound, giantProgressionCutoff_log_le ?_ hbound⟩
  apply Nat.pos_of_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro b _
  exact movingArithmeticModuli_ne_zero r p P Finset.univ
    (pow_ne_zero _ (Nat.ne_of_gt (frequencyModelBase_pos S n t (fun s hs => (hS s hs).1))))
    (fun q hq => (hP q hq).1) (fun i _ => (hp i).1) b

end Ostmann

end OAI
