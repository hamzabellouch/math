import OAI.NumberTheory.JointDickman.Amplification.RemainderPushforward

namespace OAI

/-! # Signed site tests in the removal of the two remainder restrictions -/

namespace JointDickman
open Finset

open Classical in
theorem signed_remaining_pair_error (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (g h : Finset ℕ → ℝ) (hg : ∀ S, |g S| ≤ 1) (hh : ∀ R, |h R| ≤ 1) (F : ℝ) :
    |(∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*g S*h R*
        subsetRetentionMass S A*subsetRetentionMass R D*F)-
      (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
        if RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D) then
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*g S*h R*
          subsetRetentionMass S A*subsetRetentionMass R D*F else 0)| ≤
      |F| *fairRemainingPairFailure B L τ C A D := by
  let P := auxiliaryPrimes B
  let μ := bernoulliSubsetMass P (fun p => 1/(p : ℝ))
  let w := fun S R => μ S*μ R*subsetRetentionMass S A*subsetRetentionMass R D
  let E := fun S R => RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D)
  have hμ (S : Finset ℕ) (hS : S ∈ P.powerset) : 0 ≤ μ S := by
    apply bernoulliSubsetMass_nonneg (mem_powerset.mp hS)
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
    exact ⟨by positivity,(div_le_one (by linarith)).mpr (by linarith)⟩
  have hr (S A : Finset ℕ) : 0 ≤ subsetRetentionMass S A := by
    unfold subsetRetentionMass
    split_ifs <;> positivity
  have hw (S R : Finset ℕ) (hS : S ∈ P.powerset) (hR : R ∈ P.powerset) : 0 ≤ w S R :=
    mul_nonneg (mul_nonneg (mul_nonneg (hμ S hS) (hμ R hR)) (hr S A)) (hr R D)
  have he :
      (∑ S ∈ P.powerset, ∑ R ∈ P.powerset, μ S*μ R*g S*h R*
        subsetRetentionMass S A*subsetRetentionMass R D*F)-
      (∑ S ∈ P.powerset, ∑ R ∈ P.powerset, if E S R then μ S*μ R*g S*h R*
        subsetRetentionMass S A*subsetRetentionMass R D*F else 0) =
      ∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
        if E S R then 0 else w S R*g S*h R*F := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro S _
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro R _
    dsimp only [w]
    split_ifs <;> ring
  change |(∑ S ∈ P.powerset, ∑ R ∈ P.powerset, μ S*μ R*g S*h R*
      subsetRetentionMass S A*subsetRetentionMass R D*F)-
    (∑ S ∈ P.powerset, ∑ R ∈ P.powerset, if E S R then μ S*μ R*g S*h R*
      subsetRetentionMass S A*subsetRetentionMass R D*F else 0)| ≤ _
  rw [he]
  calc
    _ ≤ ∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
        |if E S R then 0 else w S R*g S*h R*F| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun S _ => abs_sum_le_sum_abs _ _))
    _ ≤ ∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
        w S R*|F| *(if E S R then 0 else 1) := by
      apply sum_le_sum
      intro S hS
      apply sum_le_sum
      intro R hR
      by_cases hE : E S R
      · rw [ite_eq_left hE,ite_eq_left hE,abs_zero,mul_zero]
      · rw [ite_eq_right hE,ite_eq_right hE,mul_one]
        simp only [abs_mul,abs_of_nonneg (hw S R hS hR)]
        have hgh : |g S| *|h R| ≤ 1 :=
          (mul_le_mul (hg S) (hh R) (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)
        calc
          _ = w S R*(|g S| *|h R|)*|F| := by ring
          _ ≤ w S R*1*|F| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgh (hw S R hS hR))
              (abs_nonneg F)
          _ = _ := by ring
    _ = |F| *(∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
        w S R*(if E S R then 0 else 1)) := by
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro R _
      ring
    _ = _ := by
      rw [show (∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
        w S R*(if E S R then 0 else 1)) = fairRemainingPairFailure B L τ C A D from
        remainingPairFailure_site_sum B L τ C hA hD]

end JointDickman

end OAI
