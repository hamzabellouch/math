import OAI.NumberTheory.Ostmann.Characters.QuartetTreeSmallParameters
import OAI.NumberTheory.Ostmann.Characters.TreeLeafIndex

namespace OAI

/-! # Choosing the quartet gain after the actual bulk-slot counting loss -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def signedBulkGainTarget (n : ℕ) (C D : ℝ) : ℝ :=
  Real.exp (-(C + D + (2 ^ n : ℕ) * Real.log 4))

theorem signedBulkGainTarget_pos (n : ℕ) (C D : ℝ) : 0 < signedBulkGainTarget n C D :=
  Real.exp_pos _

theorem signedBulkGainTarget_absorbs (n m : ℕ) (C D : ℝ) :
    Real.exp (C * m) * 4 ^ (2 ^ n * m) * (signedBulkGainTarget n C D) ^ m =
      Real.exp (-D * m) := by
  have hfour : (4 : ℝ) ^ (2 ^ n * m) = Real.exp ((2 ^ n * m : ℕ) * Real.log 4) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  rw [hfour, signedBulkGainTarget, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- The actual number of bulk positions is `2^n*m`, while the gain is
multiplied once for each of the `m` spectator primes. -/
theorem signedBulkGainTarget_bound (n m : ℕ) (C D W A δ : ℝ)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hamp : A ≤ Real.exp (C * m)) (hgain : δ ≤ signedBulkGainTarget n C D) :
    (W * A) * 4 ^ Fintype.card (TreeLeafIndex n × Fin m) * δ ^ m ≤
      W * Real.exp (-D * m) := by
  rw [Fintype.card_prod, card_treeLeafIndex, Fintype.card_fin]
  calc
    _ ≤ (W * A) * 4 ^ (2 ^ n * m) * (signedBulkGainTarget n C D) ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ hgain m)
        (mul_nonneg (mul_nonneg hW hA) (by positivity))
    _ ≤ (W * Real.exp (C * m)) * 4 ^ (2 ^ n * m) * (signedBulkGainTarget n C D) ^ m :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hamp hW) (by positivity))
        (pow_nonneg (signedBulkGainTarget_pos n C D).le m)
    _ = _ := by rw [mul_assoc W, mul_assoc W, signedBulkGainTarget_absorbs]

/-- One fixed mixed-Fourier tolerance and one prime threshold give the gain
needed for any requested exponential rate, uniformly in the bulk length. -/
theorem exists_signedBulkGain_parameters (n : ℕ) (C D : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ N : ℕ, 3 ≤ N ∧
      ∀ p : ℕ, N ≤ p →
        3 / Real.sqrt (p : ℝ) ≤ ε ∧
        quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) ≤
          (signedBulkGainTarget (n + 2) C D) ^ 2 := by
  obtain ⟨ε, hε, hε1, N, hN, hnum⟩ := exists_quartet_small_parameters
    (quartetTreeConstant n) (signedBulkGainTarget (n + 2) C D)
    (quartetTreeConstant_pos n) (signedBulkGainTarget_pos _ _ _)
  refine ⟨ε, hε, hε1, max N ⌈(3 / ε) ^ 2⌉₊, hN.trans (le_max_left _ _), ?_⟩
  intro p hp
  have hpN : N ≤ p := (le_max_left _ _).trans hp
  refine ⟨?_, hnum p hpN⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < N) hpN)
  have hbound : (3 / ε) ^ 2 ≤ (p : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hp))
  have hsqrt : 3 / ε ≤ Real.sqrt (p : ℝ) :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr hbound
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hp0)).mpr
  have h := (div_le_iff₀ hε).mp hsqrt
  nlinarith

end Ostmann

end OAI
