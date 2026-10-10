import OAI.NumberTheory.EgyptianFractions.PrimePoolSelection
import OAI.NumberTheory.EgyptianFractions.ResidueWideDenominator
import OAI.NumberTheory.EgyptianFractions.ResidueLevels

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337.ResidueConstruction

/-- A Boolean-indexed sample block has exactly the same product as the
`Fin 2`-indexed block used to construct the common denominator.  In particular,
this conversion never removes repeated sampled primes or repeated entries. -/
theorem pairedEntry_bool_reindex {m : ℕ}
    (q : (Fin m × Bool) → ℕ) (I : Fin m → Bool) :
    pairedEntry (fun j e => q (j, finTwoEquiv e))
      (fun j => finTwoEquiv.symm (I j)) = ∏ j, q (j, I j) := by
  simp [pairedEntry]

/-- The common denominator construction in the precise Boolean sample
coordinates of the random Fourier theorem.  The fixed deterministic list is
still indexed by `Fin m → Fin 2`; the random lists retain their Boolean words. -/
theorem construct_residue_denominator_bool {m : ℕ} (p : Fin m → ℕ)
    (q : Fin 1000 → (Fin m × Bool) → ℕ)
    (hp : ∀ j, 0 < p j) (hq : ∀ i j e, 0 < q i (j, e)) {S : ℝ}
    (hS : 1 ≤ S) (hlog : 1 ≤ Real.log S)
    (hlarge : 100 * Real.log S ≤ S)
    (hmLower : S - Real.log S ≤ (m : ℝ) * Real.log S)
    (hmUpper : (m : ℝ) * Real.log S ≤ S)
    (hpBounds : ∀ j, S ^ 100 ≤ (p j : ℝ) ∧ (p j : ℝ) ≤ S ^ 101)
    (hqBounds : ∀ i j e, (q i (j, e) : ℝ) ≤ S ^ 101) :
    ∃ M : ℕ, Real.exp S < (M : ℝ) ∧ (M : ℝ) ≤ Real.exp (204204 * S) ∧
      2 ^ ⌈100000 * Real.log S / Real.log 2⌉₊ ∣ M ∧
      (∀ I : Fin m → Fin 2, subsetEntry p I ∣ M ∧ 1 ≤ subsetEntry p I ∧
        (subsetEntry p I : ℝ) ≤ Real.exp (101 * S)) ∧
      (∀ i (I : Fin m → Bool), (∏ j, q i (j, I j)) ∣ M ∧
        1 ≤ ∏ j, q i (j, I j) ∧
        ((∏ j, q i (j, I j) : ℕ) : ℝ) ≤ Real.exp (101 * S)) := by
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hpL : ∀ j, 100 * Real.log S ≤ Real.log (p j : ℝ) := by
    intro j
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (pow_pos hSpos 100) (hpBounds j).1
  have hpU : ∀ j, Real.log (p j : ℝ) ≤ 101 * Real.log S := by
    intro j
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by exact_mod_cast hp j) (hpBounds j).2
  have hqU : ∀ i j e, Real.log (q i (j, e) : ℝ) ≤ 101 * Real.log S := by
    intro i j e
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by exact_mod_cast hq i j e) (hqBounds i j e)
  obtain ⟨M, hMl, hMu, hbin, hfixed, hpaired⟩ :=
    construct_residue_denominator_wide p
      (fun i j e => q i (j, finTwoEquiv e)) hp
      (fun i j e => hq i j (finTwoEquiv e)) hS hlog hlarge hmLower hmUpper
      hpL hpU (fun i j e => hqU i j (finTwoEquiv e))
  refine ⟨M, hMl, hMu, hbin, hfixed, ?_⟩
  intro i I
  simpa only [pairedEntry_bool_reindex] using
    hpaired i (fun j => finTwoEquiv.symm (I j))

/-- Both floor-scale inequalities needed by the common denominator, without
an extra asymptotic assumption. -/
theorem scale_mul_log_bounds {S : ℝ} (hS : 0 < S) (hlog : 0 < Real.log S) :
    S - Real.log S ≤ (ResidueLevels.scale S : ℝ) * Real.log S ∧
      (ResidueLevels.scale S : ℝ) * Real.log S ≤ S := by
  have hfloor := Nat.lt_floor_add_one (S / Real.log S)
  have hlower := mul_lt_mul_of_pos_right hfloor hlog
  have hupper := mul_le_mul_of_nonneg_right
    (Nat.floor_le (div_nonneg hS.le hlog.le)) hlog.le
  rw [div_mul_cancel₀ _ hlog.ne'] at hlower hupper
  change S < ((ResidueLevels.scale S : ℝ) + 1) * Real.log S at hlower
  change (ResidueLevels.scale S : ℝ) * Real.log S ≤ S at hupper
  exact ⟨by nlinarith, hupper⟩

end Problem337.ResidueConstruction

end

end OAI
