import OAI.NumberTheory.EgyptianFractions.DeterministicSubsetMean
import OAI.NumberTheory.EgyptianFractions.DeterministicResidueSupply

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- High-level residue distribution for the canonical deterministic prime
block. The exact binary index set and all cardinality and size conditions are
discharged, so this is ready for the common-denominator construction. -/
theorem eventually_deterministic_subset_residues (D : ℝ) (hD : 255 ≤ D) :
    ∀ᶠ S : ℝ in atTop, ∀ (m : ℕ) (X : ℝ) (C : ℕ),
      S / (2 * Real.log S) ≤ (m : ℝ) → (m : ℝ) ≤ S / Real.log S →
      Real.exp S ≤ X → X ≤ Real.exp (D * S / 4) →
      Real.exp (D * S) ≤ (C : ℝ) → (C : ℝ) ≤ Real.exp (2 * D * S) →
      ∀ p : Fin m → ℕ, (∀ j, (p j).Prime) → Function.Injective p →
        (∀ j, (p j : ℝ) ≤ S ^ (101 : ℕ)) →
        ∃ E : Finset ℕ,
          E ⊆ Finset.Icc (⌊Real.exp (-(m : ℝ) / 10000) * X⌋₊ + 1) ⌊X⌋₊ ∧
          (E.card : ℝ) ≤ X * Real.exp (-(m : ℝ) / 1000) ∧
          ∀ u ∈ Finset.Icc (⌊Real.exp (-(m : ℝ) / 10000) * X⌋₊ + 1) ⌊X⌋₊,
            u ∉ E →
            Real.exp (-(m : ℝ) / 10000) * (2 : ℝ) ^ m / 2 ≤
              ((Finset.univ.filter (fun I : Fin m → Fin 2 =>
                Int.fract (-((C * ResidueConstruction.subsetEntry p I : ℕ) : ℝ) / u) <
                  Real.exp (-(m : ℝ) / 10000))).card : ℝ) := by
  filter_upwards [deterministic_high_residue_distribution D hD,
    eventually_gt_atTop (1 : ℝ)] with S hdist hS
  intro m X C hmlo hmhi hXlo hXhi hClo hChi p hp hinj hsize
  have hcard : Real.exp (Real.log 2 * (m : ℝ)) ≤
      ((Finset.univ : Finset (Fin m → Fin 2)).card : ℝ) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    simp
  have hh := hdist m X C hmlo hmhi hXlo hXhi hClo hChi
    (Finset.univ : Finset (Fin m → Fin 2)) (ResidueConstruction.subsetEntry p)
    (ResidueConstruction.subsetEntry_injective p hp hinj).injOn hcard
    (fun I _ => subsetEntry_le_exp_of_power_pool hS hmhi p hp hsize I)
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat] using hh

/-- Compatibility name for the identical independently assembled subset endpoint.
The canonical proof is shared rather than duplicated. -/
alias deterministic_subset_residue_distribution := eventually_deterministic_subset_residues

end Problem337

end

end OAI
