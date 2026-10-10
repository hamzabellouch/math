import OAI.NumberTheory.JointDickman.Probability.FairSplitPairRegularity
import OAI.NumberTheory.JointDickman.Probability.SignedChannelMass

namespace OAI

/-! # The exact selected-and-remaining law behind the candidate error -/

namespace JointDickman
open Finset

open Classical in
theorem selectedRemainingMass_site {P S A : Finset ℕ} (hA : A ⊆ S) :
    bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S*subsetRetentionMass S A =
      fairSelectedRemainingMass P A (S \ A) := by
  have hd : Disjoint A (S \ A) := by
    apply disjoint_left.mpr
    intro p hp hps
    exact (mem_sdiff.mp hps).2 hp
  simp only [subsetRetentionMass,ite_eq_left hA,fairSelectedRemainingMass,
    ite_eq_left hd,union_sdiff_of_subset hA]

open Classical in
/-- Replacing a site by its selected set and its complement is an exact
change of variables. The test can be a regularity failure indicator. -/
theorem selectedRemainingMass_sum {P A : Finset ℕ} (hA : A ⊆ P)
    (F : Finset ℕ → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S*
      subsetRetentionMass S A*F (S \ A)) =
      ∑ R ∈ P.powerset, fairSelectedRemainingMass P A R*F R := by
  have hsub : (P \ A).powerset ⊆ P.powerset := by
    intro R hR
    exact mem_powerset.mpr ((mem_powerset.mp hR).trans sdiff_subset)
  have hext : (∑ R ∈ (P \ A).powerset, fairSelectedRemainingMass P A R*F R) =
      ∑ R ∈ P.powerset, fairSelectedRemainingMass P A R*F R := by
    apply sum_subset hsub
    intro R hR hn
    have hd : ¬ Disjoint A R := by
      intro hd
      apply hn
      apply mem_powerset.mpr
      intro p hp
      exact mem_sdiff.mpr ⟨mem_powerset.mp hR hp,
        fun ha => disjoint_left.mp hd ha hp⟩
    simp only [fairSelectedRemainingMass,ite_eq_right hd,zero_mul]
  rw [← hext]
  calc
    _ = ∑ S ∈ P.powerset.filter (fun S => A ⊆ S),
        bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S*subsetRetentionMass S A*F (S \ A) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro S _
      by_cases hs : A ⊆ S
      · rw [ite_eq_left hs]
      · simp only [subsetRetentionMass,ite_eq_right hs,mul_zero,zero_mul]
    _ = _ := by
      apply sum_bij (fun S _ => S \ A)
      · intro S hS
        exact mem_powerset.mpr (sdiff_subset_sdiff
          (mem_powerset.mp (mem_filter.mp hS).1) subset_rfl)
      · intro S hS T hT he
        have hs := sdiff_union_of_subset (mem_filter.mp hS).2
        have ht := sdiff_union_of_subset (mem_filter.mp hT).2
        rw [he] at hs
        exact hs.symm.trans ht
      · intro R hR
        have hr := mem_powerset.mp hR
        refine ⟨A ∪ R,mem_filter.mpr ⟨mem_powerset.mpr
          (union_subset hA (hr.trans sdiff_subset)),subset_union_left⟩,?_⟩
        ext p
        have hp : p ∈ R → p ∉ A := fun h => (mem_sdiff.mp (hr h)).2
        simp only [mem_sdiff,mem_union]
        tauto
      · intro S hS
        rw [selectedRemainingMass_site (mem_filter.mp hS).2]


open Classical in
theorem selectedRemainingMass_pair_sum {P A D : Finset ℕ} (hA : A ⊆ P) (hD : D ⊆ P)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ S ∈ P.powerset, ∑ R ∈ P.powerset,
      bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S*
      bernoulliSubsetMass P (fun p => 1/(p : ℝ)) R*
      subsetRetentionMass S A*subsetRetentionMass R D*F (S \ A) (R \ D)) =
      ∑ U ∈ P.powerset, ∑ V ∈ P.powerset,
        fairSelectedRemainingMass P A U*fairSelectedRemainingMass P D V*F U V := by
  calc
    _ = ∑ S ∈ P.powerset,
        bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S*subsetRetentionMass S A*
          (∑ R ∈ P.powerset, bernoulliSubsetMass P (fun p => 1/(p : ℝ)) R*
            subsetRetentionMass R D*F (S \ A) (R \ D)) := by
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro R _
      ring
    _ = ∑ S ∈ P.powerset,
        bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S*subsetRetentionMass S A*
          (∑ V ∈ P.powerset, fairSelectedRemainingMass P D V*F (S \ A) V) := by
      simp_rw [selectedRemainingMass_sum hD]
    _ = ∑ U ∈ P.powerset, fairSelectedRemainingMass P A U*
        (∑ V ∈ P.powerset, fairSelectedRemainingMass P D V*F U V) :=
      selectedRemainingMass_sum hA (fun U =>
        ∑ V ∈ P.powerset, fairSelectedRemainingMass P D V*F U V)
    _ = _ := by simp_rw [mul_sum,mul_assoc]

open Classical in
/-- The bad-remainder event in the site-first expression is exactly the
failure mass whose conditional probability is controlled by Mertens. -/
theorem remainingPairFailure_site_sum (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
      subsetRetentionMass S A*subsetRetentionMass R D*
        (if RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D)
          then 0 else 1)) = fairRemainingPairFailure B L τ C A D := by
  rw [selectedRemainingMass_pair_sum hA hD (fun U V =>
    if RegularPrimeSet B L τ C U ∧ RegularPrimeSet B L τ C V then 0 else 1)]
  unfold fairRemainingPairFailure
  apply sum_congr rfl
  intro U _
  apply sum_congr rfl
  intro V _
  split_ifs <;> simp only [mul_zero,mul_one]

end JointDickman

end OAI
