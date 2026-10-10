import OAI.NumberTheory.JointDickman.Amplification.CandidateCollisionGeometry
import OAI.NumberTheory.JointDickman.Amplification.IndependentForcedHits

namespace OAI

/-! # The conditional probability of a repeated candidate root -/

namespace JointDickman
open Finset PublishedInputs

open Classical in
abbrev OtherCandidateSite {M : ℕ} (e : BlockCandidateIndex M) :=
  {s : Fin M // s ≠ e.1.1 ∧ s ≠ e.1.2}

open Classical in
theorem finiteProbability_eq_indicator_mean {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (E : Ω → Prop) :
    finiteProbability w E = finiteExpectation w (fun x => if E x then 1 else 0) := by
  simp only [finiteProbability,finiteExpectation,mul_ite,mul_one,mul_zero]

open Classical in
theorem independent_available_probability {B n : ℕ} {X : ℝ} (hX : 0 < X) (hn : X ≤ n) :
    finiteProbability (independentPrimeSetMass B) (fun R => PrimeProductAvailable n R.val) ≤ 1/X := by
  have hh := independent_site_large_available_le (auxiliaryPrimes B) (auxiliaryPrimes_prime B) hX hn
  have he : finiteProbability (independentPrimeSetMass B) (fun R => PrimeProductAvailable n R.val) =
      ∑ S ∈ (auxiliaryPrimes B).powerset, if PrimeProductAvailable n S then
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S else 0 := by
    exact sum_coe_sort (auxiliaryPrimes B).powerset (fun S =>
      if PrimeProductAvailable n S then bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S else 0)
  exact he.trans_le hh

open Classical in
/-- This estimate conditions only on the candidate's two endpoints. Each
remaining endpoint is still sampled with its original independent law. -/
theorem candidate_third_site_probability {B L T H M : ℕ} {τ C : ℝ}
    (hT : 0 < T) {e : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e) :
    finiteProbability (siteProductMass (fun _ : OtherCandidateSite e => independentPrimeSetMass B))
      (fun S => ∃ s : OtherCandidateSite e,
        T*candidateQuotient e ≤ (candidateSiteValue e s.val).natAbs ∧
        PrimeProductAvailable (candidateSiteValue e s.val).natAbs (S s).val) ≤
      (M : ℝ)/((T : ℝ)*candidateQuotient e) := by
  let w := siteProductMass (fun _ : OtherCandidateSite e => independentPrimeSetMass B)
  let X : ℝ := (T : ℝ)*candidateQuotient e
  have hX : 0 < X := mul_pos (by exact_mod_cast hT) (by exact_mod_cast he.2.2.2.1)
  have hs (s : OtherCandidateSite e) : finiteProbability w
      (fun S => T*candidateQuotient e ≤ (candidateSiteValue e s.val).natAbs ∧
        PrimeProductAvailable (candidateSiteValue e s.val).natAbs (S s).val) ≤ 1/X := by
    by_cases hn : T*candidateQuotient e ≤ (candidateSiteValue e s.val).natAbs
    · simp only [hn,true_and]
      rw [finiteProbability_eq_indicator_mean]
      have hcoord := siteProduct_expectation_coordinate
        (fun _ : OtherCandidateSite e => independentPrimeSetMass B)
        (fun _ => independentPrimeSetMass_sum B) s
        (fun R : (auxiliaryPrimes B).powerset =>
          if PrimeProductAvailable (candidateSiteValue e s.val).natAbs R.val then (1 : ℝ) else 0)
      change finiteExpectation (siteProductMass (fun _ : OtherCandidateSite e => independentPrimeSetMass B))
        (fun S => if PrimeProductAvailable (candidateSiteValue e s.val).natAbs (S s).val then 1 else 0) ≤ _
      rw [hcoord,← finiteProbability_eq_indicator_mean]
      exact independent_available_probability hX (by dsimp [X]; exact_mod_cast hn)
    · simp only [hn,false_and,finiteProbability,ite_false,sum_const_zero]
      exact one_div_nonneg.mpr hX.le
  calc
    _ ≤ ∑ s : OtherCandidateSite e, finiteProbability w
        (fun S => T*candidateQuotient e ≤ (candidateSiteValue e s.val).natAbs ∧
          PrimeProductAvailable (candidateSiteValue e s.val).natAbs (S s).val) :=
      finiteProbability_union_le w
        (siteProductMass_nonneg _ (fun _ => independentPrimeSetMass_nonneg B)) _
    _ ≤ ∑ _s : OtherCandidateSite e, 1/X := sum_le_sum (fun s _ => hs s)
    _ = (Fintype.card (OtherCandidateSite e) : ℝ)/X := by simp [div_eq_mul_inv]
    _ ≤ (M : ℝ)/X := div_le_div_of_nonneg_right
      (by exact_mod_cast (show Fintype.card (OtherCandidateSite e) ≤ M from by
        simpa only [Fintype.card_fin] using
          Fintype.card_subtype_le (fun s : Fin M => s ≠ e.1.1 ∧ s ≠ e.1.2))) hX.le
    _ = _ := rfl

end JointDickman

end OAI
