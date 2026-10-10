import OAI.NumberTheory.JointDickman.Amplification.SignedRemainderError
import OAI.NumberTheory.JointDickman.Amplification.RemainderFailureWeight

namespace OAI

/-! # Removing remainder regularity in the actual finite retention kernel -/

namespace JointDickman
open Finset

noncomputable def retainedSubsetKernel (P : Finset ℕ) (F : Finset ℕ → Finset ℕ → ℝ)
    (S R : Finset ℕ) : ℝ :=
  ∑ A ∈ P.powerset, ∑ D ∈ P.powerset, subsetRetentionMass S A*subsetRetentionMass R D*F A D

open Classical in
noncomputable def regularRemainderKernel (B L : ℕ) (τ C : ℝ)
    (F : Finset ℕ → Finset ℕ → ℝ) (S R : Finset ℕ) : ℝ :=
  ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
    if RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D) then
      subsetRetentionMass S A*subsetRetentionMass R D*F A D else 0

private theorem four_subset_sums_swap (P : Finset ℕ)
    (f : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ S ∈ P.powerset, ∑ R ∈ P.powerset, ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
      f S R A D) =
    ∑ A ∈ P.powerset, ∑ D ∈ P.powerset, ∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
      f S R A D := by
  conv_lhs => arg 2; ext S; rw [sum_comm]
  rw [sum_comm]
  conv_lhs => arg 2; ext A; arg 2; ext S; rw [sum_comm]
  conv_lhs => arg 2; ext A; rw [sum_comm]

open Classical in
theorem retentionKernel_remaining_error (B L : ℕ) (τ C : ℝ)
    (F : Finset ℕ → Finset ℕ → ℝ)
    (g h : Finset ℕ → ℝ) (hg : ∀ S, |g S| ≤ 1) (hh : ∀ R, |h R| ≤ 1) :
    |(∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*g S*h R*
          retainedSubsetKernel (auxiliaryPrimes B) F S R)-
      (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*g S*h R*
          regularRemainderKernel B L τ C F S R)| ≤
      ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        |F A D| *fairRemainingPairFailure B L τ C A D := by
  let P := auxiliaryPrimes B
  let μ := bernoulliSubsetMass P (fun p => 1/(p : ℝ))
  let v := fun S R A D => μ S*μ R*g S*h R*subsetRetentionMass S A*subsetRetentionMass R D*F A D
  let E := fun S R A D => RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D)
  have he :
      (∑ S ∈ P.powerset, ∑ R ∈ P.powerset, μ S*μ R*g S*h R*retainedSubsetKernel P F S R)-
      (∑ S ∈ P.powerset, ∑ R ∈ P.powerset, μ S*μ R*g S*h R*regularRemainderKernel B L τ C F S R) =
      ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
        ((∑ S ∈ P.powerset, ∑ R ∈ P.powerset, v S R A D)-
          ∑ S ∈ P.powerset, ∑ R ∈ P.powerset, if E S R A D then v S R A D else 0) := by
    have hfull : (∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
        μ S*μ R*g S*h R*retainedSubsetKernel P F S R) =
        ∑ A ∈ P.powerset, ∑ D ∈ P.powerset, ∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
          v S R A D := by
      rw [← four_subset_sums_swap]
      unfold retainedSubsetKernel
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro R _
      apply sum_congr rfl
      intro A _
      apply sum_congr rfl
      intro D _
      dsimp only [v]
      ring
    have hregular : (∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
        μ S*μ R*g S*h R*regularRemainderKernel B L τ C F S R) =
        ∑ A ∈ P.powerset, ∑ D ∈ P.powerset, ∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
          if E S R A D then v S R A D else 0 := by
      rw [← four_subset_sums_swap]
      unfold regularRemainderKernel
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro R _
      apply sum_congr rfl
      intro A _
      apply sum_congr rfl
      intro D _
      dsimp only [v,E]
      split_ifs <;> ring
    rw [hfull,hregular,← sum_sub_distrib]
    apply sum_congr rfl
    intro A _
    rw [sum_sub_distrib]
  change |(∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
      μ S*μ R*g S*h R*retainedSubsetKernel P F S R)-
    (∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
      μ S*μ R*g S*h R*regularRemainderKernel B L τ C F S R)| ≤ _
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro A hA
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro D hD
  exact signed_remaining_pair_error B L τ C (mem_powerset.mp hA) (mem_powerset.mp hD) g h hg hh (F A D)

end JointDickman

end OAI
