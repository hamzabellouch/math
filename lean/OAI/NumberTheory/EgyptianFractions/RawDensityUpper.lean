import OAI.NumberTheory.EgyptianFractions.DensityAssembly
import OAI.NumberTheory.EgyptianFractions.MainUpperReduction

namespace OAI
noncomputable section
open Filter

namespace Problem337

/-- The remaining arithmetic supply interface for the main upper bound.
The residue distribution and shifted divisor moments are explicit fields of
`DensityResidueFamily`; this definition does not assert their existence. -/
def RawDensitySupply (DM L c K r S : ℝ) (C : ℕ) : Prop :=
  ∃ (m ρ : ℝ) (d : ℕ) (F : DensityResidueFamily S m ρ r c d),
    S / (2 * Real.log S) ≤ m ∧ (d : ℝ) ≤ K * Real.log S ∧
    0 < ρ ∧ ρ ≤ 1 ∧
    ((F.baseLength + d : ℕ) : ℝ) ≤ L * Real.log S ∧
    F.cutoff 0 = Real.exp ((DM + 2) * S) ∧ F.factor 0 = C ∧
    Real.exp S < (F.denominator : ℝ) ∧
    (F.denominator : ℝ) ≤ Real.exp (DM * S)

/-- The checked density descent supplies exactly the input to the elementary
main-upper reduction. No additional fraction-size hypothesis is needed. -/
theorem eventually_dense_family_of_raw_supply
    (DM L c K r : ℝ) (hDM : 1 < DM) (hc : 0 < c) (hK : 0 ≤ K)
    (hr : 2 ≤ r) (hKr : 8 * K ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      RawDensitySupply DM L c K r S C → DenseEgyptianFamily DM L S C := by
  filter_upwards [eventually_residue_family_dense_lists c K r hc hK hr hKr,
    eventually_ge_atTop (1 : ℝ)] with S hS hS1
  intro C hC hraw
  obtain ⟨m, ρ, d, F, hm, hd, hρ0, hρ1, hlen, hcut, hfactor, hMlow, hMup⟩ := hraw
  have hfrac : F.cutoff 0 < ((F.denominator * F.factor 0 : ℕ) : ℝ) := by
    rw [hcut, hfactor]
    have hX : Real.exp ((DM + 2) * S) < Real.exp (4 * (DM + 2) * S) := by
      apply Real.exp_lt_exp.mpr
      nlinarith
    have hMone : (1 : ℝ) ≤ F.denominator := by
      exact_mod_cast F.denominator_pos
    have hprod : (C : ℝ) ≤ ((F.denominator * C : ℕ) : ℝ) := by
      push_cast
      simpa using mul_le_mul_of_nonneg_right hMone (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
    exact hX.trans_le (hC.trans hprod)
  obtain ⟨G, hholes, hG⟩ := hS m ρ L d F hm hd hρ0 hρ1 hlen hfrac
  refine ⟨F.denominator, G, hMlow, hMup, ?_, ?_⟩
  · simpa only [hcut] using hholes
  · simpa only [hfactor] using hG

/-- Final composition of the two checked reductions. The sole remaining
construction premise is eventual existence of the raw arithmetic supply. -/
theorem main_upper_of_raw_density_supply
    (DM L c K r : ℝ) (hDM : 1 < DM) (hL : 0 < L)
    (hc : 0 < c) (hK : 0 ≤ K) (hr : 2 ≤ r) (hKr : 8 * K ≤ r)
    (hsupply : ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
      RawDensitySupply DM L c K r S C) :
    ∃ c2 : ℝ, 0 < c2 ∧ ∃ b0 : ℕ, ∀ b : ℕ, b0 ≤ b →
      (maxEgyptianLength b : ℝ) ≤ c2 * Real.log (Real.log (b : ℝ)) := by
  have hdense : ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
      DenseEgyptianFamily DM L S C := by
    filter_upwards [hsupply,
      eventually_dense_family_of_raw_supply DM L c K r hDM hc hK hr hKr] with S hraw hS
    intro C hClow hCup
    exact hS C hClow (hraw C hClow hCup)
  obtain ⟨S0, hS0⟩ := eventually_atTop.mp hdense
  exact main_upper_of_dense_family DM L S0 hDM hL hS0

end Problem337


end

end OAI
