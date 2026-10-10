import OAI.NumberTheory.JointDickman.Probability.CandidateThirdSiteProbability

namespace OAI

/-! # Prescribed large coefficients across any remaining site set -/

namespace JointDickman
open Finset PublishedInputs

open Classical in
theorem independent_large_coefficients_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B N : ℕ) (hN : 0 < N) (n : ι → ℕ) :
    finiteProbability (siteProductMass (fun _ : ι => independentPrimeSetMass B))
      (fun S => ∃ s, N ≤ n s ∧ PrimeProductAvailable (n s) (S s).val) ≤
        (Fintype.card ι : ℝ)/(N : ℝ) := by
  let w := siteProductMass (fun _ : ι => independentPrimeSetMass B)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs (s : ι) : finiteProbability w
      (fun S => N ≤ n s ∧ PrimeProductAvailable (n s) (S s).val) ≤ 1/(N : ℝ) := by
    by_cases hn : N ≤ n s
    · simp only [hn,true_and]
      rw [finiteProbability_eq_indicator_mean]
      change finiteExpectation (siteProductMass (fun _ : ι => independentPrimeSetMass B))
        (fun S => if PrimeProductAvailable (n s) (S s).val then 1 else 0) ≤ _
      rw [siteProduct_expectation_coordinate _ (fun _ => independentPrimeSetMass_sum B) s
        (fun R => if PrimeProductAvailable (n s) R.val then 1 else 0),
        ← finiteProbability_eq_indicator_mean]
      exact independent_available_probability hNr (by exact_mod_cast hn)
    · simp only [hn,false_and,finiteProbability,ite_false,sum_const_zero]
      exact one_div_nonneg.mpr hNr.le
  calc
    _ ≤ ∑ s : ι, finiteProbability w
        (fun S => N ≤ n s ∧ PrimeProductAvailable (n s) (S s).val) :=
      finiteProbability_union_le w
        (siteProductMass_nonneg _ (fun _ => independentPrimeSetMass_nonneg B)) _
    _ ≤ ∑ _s : ι, 1/(N : ℝ) := sum_le_sum (fun s _ => hs s)
    _ = _ := by simp [div_eq_mul_inv]

end JointDickman

end OAI
