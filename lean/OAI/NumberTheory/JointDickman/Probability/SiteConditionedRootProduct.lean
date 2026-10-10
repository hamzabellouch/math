import OAI.NumberTheory.JointDickman.Amplification.OccupiedRootComparison

namespace OAI

/-! # Independent prime product after conditioning the endpoint sites -/

namespace JointDickman
open Finset

noncomputable def siteConditionedRootProductMass {M : ℕ} (B : ℕ)
    (I : Finset (BlockCandidateIndex M)) (S : Fin M → Finset ℕ)
    (R : auxiliaryPrimes B → I.powerset) : ℝ :=
  finiteProductMass (fun p : auxiliaryPrimes B => @siteConditionedRootPrimeMass M I S p.val
    ⟨auxiliaryPrimes_prime B p.val p.property⟩) R

open Classical in
theorem siteConditionedRootProduct_l1 {B M : ℕ} (I : Finset (BlockCandidateIndex M))
    (S : Fin M → Finset ℕ) (hsize : ∀ p ∈ auxiliaryPrimes B, M < p)
    (hhalf : ∀ p ∈ auxiliaryPrimes B, 2*M ≤ p) :
    (∑ R, |siteConditionedRootProductMass B I S R-
      bernoulliProductMass I (fun p : auxiliaryPrimes B => fun _ => 1/(p.val : ℝ)) R|) ≤
      8*((I.card : ℝ)+(M : ℝ))^2*(∑ p ∈ auxiliaryPrimes B, 1/(p : ℝ)^2)+
      6*(I.card : ℝ)*(∑ p ∈ candidateDefectPrimes B I, 1/(p : ℝ))+
      2*(I.card : ℝ)*occupiedPrimeReciprocalMass B S := by
  let a := fun p : auxiliaryPrimes B => @siteConditionedRootPrimeMass M I S p.val
    ⟨auxiliaryPrimes_prime B p.val p.property⟩
  let b := fun p : auxiliaryPrimes B => fun R : I.powerset =>
    bernoulliSubsetMass I (fun _ => 1/(p.val : ℝ)) R.val
  have ha (p : auxiliaryPrimes B) (R : I.powerset) : 0 ≤ a p R := by
    let : Fact p.val.Prime := ⟨auxiliaryPrimes_prime B p.val p.property⟩
    exact siteConditionedRootPrimeMass_nonneg I S p.val R
  have haone (p : auxiliaryPrimes B) : ∑ R, a p R = 1 := by
    let : Fact p.val.Prime := ⟨auxiliaryPrimes_prime B p.val p.property⟩
    exact siteConditionedRootPrimeMass_sum I S p.val (hsize p.val p.property)
  have hb (p : auxiliaryPrimes B) (R : I.powerset) : 0 ≤ b p R := by
    apply bernoulliSubsetMass_nonneg (mem_powerset.mp R.property)
    intro _ _
    have hp : (1 : ℝ) ≤ p.val := by exact_mod_cast (auxiliaryPrimes_prime B p.val p.property).one_le
    exact ⟨by positivity,(div_le_one (by linarith)).mpr hp⟩
  have hbone (p : auxiliaryPrimes B) : ∑ R, b p R = 1 :=
    (sum_coe_sort _ _).trans (bernoulliSubsetMass_sum _ _)
  let F := fun p : ℕ => 8*((I.card : ℝ)+(M : ℝ))^2/(p : ℝ)^2+
    (if p ∈ candidateDefectPrimes B I then 6*(I.card : ℝ)/(p : ℝ) else 0)+
    (if ∃ i, p ∈ S i then 2*(I.card : ℝ)/(p : ℝ) else 0)
  have hlocal (p : auxiliaryPrimes B) : (∑ R, |a p R-b p R|) ≤ F p.val :=
    @siteConditionedRootPrimeMass_l1 B M p.val
      ⟨auxiliaryPrimes_prime B p.val p.property⟩ I S p.property
      (hsize p.val p.property) (hhalf p.val p.property)
  have hdef : (auxiliaryPrimes B).filter (fun p => p ∈ candidateDefectPrimes B I) ⊆
      candidateDefectPrimes B I := fun _ hp => (mem_filter.mp hp).2
  have hrec : (∑ p ∈ auxiliaryPrimes B, if p ∈ candidateDefectPrimes B I then 1/(p : ℝ) else 0) ≤
      ∑ p ∈ candidateDefectPrimes B I, 1/(p : ℝ) := by
    rw [← sum_filter]
    exact sum_le_sum_of_subset_of_nonneg hdef (fun _ _ _ => by positivity)
  calc
    _ ≤ ∑ p : auxiliaryPrimes B, ∑ R, |a p R-b p R| :=
      finiteProductMass_l1_le a b ha hb haone hbone
    _ ≤ ∑ p : auxiliaryPrimes B, F p.val := sum_le_sum (fun p _ => hlocal p)
    _ = ∑ p ∈ auxiliaryPrimes B, F p := sum_coe_sort _ F
    _ = 8*((I.card : ℝ)+(M : ℝ))^2*(∑ p ∈ auxiliaryPrimes B, 1/(p : ℝ)^2)+
        6*(I.card : ℝ)*(∑ p ∈ auxiliaryPrimes B, if p ∈ candidateDefectPrimes B I then 1/(p : ℝ) else 0)+
        2*(I.card : ℝ)*occupiedPrimeReciprocalMass B S := by
      simp only [F,occupiedPrimeReciprocalMass,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro p _
      split_ifs <;> ring
    _ ≤ _ := add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hrec (by positivity))) le_rfl

end JointDickman

end OAI
