import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyModulus
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # All CRT size conditions for the concrete pair frequency modulus -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- A single eventual cutoff works for every actual history, frequency
choice and spectator list in the prescribed ranges. -/
theorem moving_pair_modulus_range (n k : ℕ) (A a : ℝ) (hA : 0 ≤ A) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (σ : Type) (T : Bool → MovingSlotData σ n) (B : ℕ) (p : Fin m → ℕ),
      (∀ b, (T b).Frequencies (· ≠ 0)) →
      (∀ b, (T b).Frequencies (fun s => s.natAbs ≤ B)) →
      (B : ℝ) ≤ Real.exp (A * m) →
      (∀ i, (p i).Prime) → Function.Injective p →
      (∀ i, Real.exp (Real.exp (a * L)) ≤ (p i : ℝ)) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      let r := movingPairFrequencyModulus T
      let M := ∏ i, bulkResidueModuli r p i
      0 < r ∧
      (∀ b, (T b).frequencyProduct ∣ movingPairFrequencyBase T) ∧
      movingPairFrequencyBase T ^ (n + 1) ∣ (r : ℤ) ∧
      Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)) ∧
      0 < M ∧ M ≤ bulkProgressionCutoff L ∧
      (∀ u : ℝ, Real.exp ((39 / 10000 : ℝ) * L) ≤ u → (M : ℝ) ≤ Real.exp u) := by
  let C : ℝ := (2 * (2 ^ (n + 1) - 1) * (n + 1) : ℕ) * A
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) hA
  have hK : 0 ≤ (k : ℝ) ^ 4 := by positivity
  filter_upwards [frequency_modulus_lt_spectators C ((k : ℝ) ^ 4) a hC hK ha,
    bulkResidueModulus_progression_range C ((k : ℝ) ^ 4) hC hK,
    eventually_ge_atTop (0 : ℝ)] with L hlt hrange hL
  dsimp only
  intro σ T B p hf hB hBexp hp hinj hplower hpupper
  let r := movingPairFrequencyModulus T
  have hr : 0 < r := movingPairFrequencyModulus_pos T hf
  have hrex : (r : ℝ) ≤ Real.exp (C * spectatorBulkCount k L) := by
    simpa only [C, mul_assoc] using movingPairFrequencyModulus_exp T B A _ hB hBexp
  have hm := spectatorBulkCount_upper k L hL
  have hri := hlt _ r p hm hrex hplower
  have hM := hrange _ r p hm hrex hpupper
  refine ⟨hr, movingPairFrequencyBase_dvd T, movingPairFrequencyModulus_precision T,
    bulkResidueModuli_pairwise_of_lt r hr p hp hinj hri,
    bulkResidueModulus_positive r hr p (fun i => (hp i).pos), hM, ?_⟩
  intro u hu
  apply (Nat.cast_le.mpr hM).trans
  apply (Nat.floor_le (Real.exp_nonneg _)).trans
  apply Real.exp_le_exp.mpr
  apply le_trans _ hu
  exact Real.exp_le_exp.mpr (by linarith)

end Ostmann

end OAI
