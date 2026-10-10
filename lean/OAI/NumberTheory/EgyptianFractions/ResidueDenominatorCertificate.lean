import OAI.NumberTheory.EgyptianFractions.PrimePoolSelection
import OAI.NumberTheory.EgyptianFractions.ResidueWideDenominator
import OAI.NumberTheory.EgyptianFractions.ResidueLevels

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337.ResidueConstruction

/-- Uniform arithmetic certificate for the common residue denominator.
The deterministic prime vector is chosen before the random blocks. Every
realization with the stated factor bounds has a suitable common denominator;
there is no prime-density, floor-scale, or logarithmic-size premise left. -/
theorem eventually_residue_denominator_certificate :
    ∀ᶠ S : ℝ in atTop,
      ∃ p : Fin (ResidueLevels.scale S) → ℕ,
        Function.Injective p ∧
        (∀ j, Nat.Prime (p j) ∧ S ^ 100 < (p j : ℝ) ∧ (p j : ℝ) ≤ S ^ 101) ∧
        Function.Injective (subsetEntry p) ∧
        ∀ q : Fin 1000 → Fin (ResidueLevels.scale S) → Fin 2 → ℕ,
          (∀ i j e, 0 < q i j e) →
          (∀ i j e, (q i j e : ℝ) ≤ S ^ 101) →
          ∃ M : ℕ, Real.exp S < (M : ℝ) ∧
            (M : ℝ) ≤ Real.exp (204204 * S) ∧
            2 ^ ⌈100000 * Real.log S / Real.log 2⌉₊ ∣ M ∧
            (∀ I : Fin (ResidueLevels.scale S) → Fin 2,
              subsetEntry p I ∣ M ∧ 1 ≤ subsetEntry p I ∧
                (subsetEntry p I : ℝ) ≤ Real.exp (101 * S)) ∧
            (∀ i (I : Fin (ResidueLevels.scale S) → Fin 2),
              pairedEntry (q i) I ∣ M ∧ 1 ≤ pairedEntry (q i) I ∧
                (pairedEntry (q i) I : ℝ) ≤ Real.exp (101 * S)) := by
  filter_upwards [eventually_residue_prime_vector,
    ResidueLevels.eventually_scale_bounds,
    ResidueLevels.tendsto_div_log.eventually (eventually_ge_atTop (100 : ℝ)),
    eventually_ge_atTop (3 : ℝ)] with S hp hscale hratio hS
  obtain ⟨p, hinj, hp, hsub, _⟩ := hp
  have hp' : ∀ j, Nat.Prime (p j) ∧ S ^ 100 < (p j : ℝ) ∧
      (p j : ℝ) ≤ S ^ 101 := hp
  refine ⟨p, hinj, hp', hsub, ?_⟩
  intro q hq hqU
  have hSp : 0 < S := by linarith
  have hlog : 0 < Real.log S := by linarith [hscale.1]
  have hlarge : 100 * Real.log S ≤ S := (le_div_iff₀ hlog).mp hratio
  have hmUpper : (ResidueLevels.scale S : ℝ) * Real.log S ≤ S :=
    (le_div_iff₀ hlog).mp hscale.2.2.2
  have hf := Nat.lt_floor_add_one (S / Real.log S)
  change S / Real.log S < (ResidueLevels.scale S : ℝ) + 1 at hf
  have hmLower : S - Real.log S ≤ (ResidueLevels.scale S : ℝ) * Real.log S := by
    have hf' := (div_lt_iff₀ hlog).mp hf
    nlinarith
  have hpPos : ∀ j, 0 < p j := fun j => (hp j).1.pos
  have hpLogLower : ∀ j, 100 * Real.log S ≤ Real.log (p j : ℝ) := by
    intro j
    have h := Real.log_le_log (pow_pos hSp 100) (hp j).2.1.le
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hpLogUpper : ∀ j, Real.log (p j : ℝ) ≤ 101 * Real.log S := by
    intro j
    have h := Real.log_le_log (by exact_mod_cast hpPos j) (hp j).2.2
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hqLogUpper : ∀ i j e, Real.log (q i j e : ℝ) ≤ 101 * Real.log S := by
    intro i j e
    have h := Real.log_le_log (by exact_mod_cast hq i j e) (hqU i j e)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  exact construct_residue_denominator_wide p q hpPos hq (by linarith) hscale.1
    hlarge hmLower hmUpper hpLogLower hpLogUpper hqLogUpper

end Problem337.ResidueConstruction

end

end OAI
