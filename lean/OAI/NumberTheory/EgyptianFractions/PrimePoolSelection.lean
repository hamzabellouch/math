import OAI.NumberTheory.EgyptianFractions.PrimePool
import OAI.NumberTheory.EgyptianFractions.ResidueDenominator

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- Select the deterministic prime vector of length `floor(S/log S)` from the
proved elementary prime pool. -/
theorem eventually_residue_prime_vector :
    ∀ᶠ S : ℝ in atTop,
      ∃ p : Fin ⌊S / Real.log S⌋₊ → ℕ,
        Function.Injective p ∧
        (∀ i, Nat.Prime (p i) ∧ S ^ 100 < (p i : ℝ) ∧ (p i : ℝ) ≤ S ^ 101) ∧
        Function.Injective (ResidueConstruction.subsetEntry p) ∧
        (Finset.univ.image (ResidueConstruction.subsetEntry p)).card = 2 ^ ⌊S / Real.log S⌋₊ := by
  filter_upwards [eventually_residue_prime_pool_spec,
    eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (Real.exp 1)] with S hpool hS hSexp
  have hSpos : 0 < S := by linarith
  have hlogS : 1 ≤ Real.log S := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log S := Real.log_le_log (Real.exp_pos 1) hSexp
  have hmreal : (⌊S / Real.log S⌋₊ : ℝ) ≤ S := by
    calc
      (⌊S / Real.log S⌋₊ : ℝ) ≤ S / Real.log S := Nat.floor_le (by positivity)
      _ ≤ S := div_le_self hSpos.le hlogS
  have hSpow : S ≤ S ^ 99 := by
    have hh : 1 ≤ S ^ 98 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ S)
    calc
      S = S * 1 := by ring
      _ ≤ S * S ^ 98 := mul_le_mul_of_nonneg_left hh hSpos.le
      _ = S ^ 99 := by ring
  have hmcard : ⌊S / Real.log S⌋₊ ≤ (widePrimePool (S ^ 100)).card := by
    exact_mod_cast hmreal.trans (hSpow.trans hpool.1)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin ⌊S / Real.log S⌋₊) (β := ↥(widePrimePool (S ^ 100))) (by simpa using hmcard)
  let p : Fin ⌊S / Real.log S⌋₊ → ℕ := fun i => (e i).val
  have hinj : Function.Injective p := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have hp : ∀ i, Nat.Prime (p i) ∧ S ^ 100 < (p i : ℝ) ∧ (p i : ℝ) ≤ S ^ 101 := by
    intro i
    exact hpool.2 (p i) (e i).property
  exact ⟨p, hinj, hp, ResidueConstruction.subsetEntry_injective p (fun i => (hp i).1) hinj,
    ResidueConstruction.subsetEntry_image_card p (fun i => (hp i).1) hinj⟩

end Problem337

end

end OAI
