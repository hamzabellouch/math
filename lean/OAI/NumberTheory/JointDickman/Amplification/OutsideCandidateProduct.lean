import OAI.NumberTheory.JointDickman.Amplification.OutsideCandidateMass

namespace OAI

/-! # Product comparison over the unoccupied primes -/

namespace JointDickman
open Finset

noncomputable def outsideCandidateProductMass {M : ℕ} (B : ℕ)
    (I : Finset (BlockCandidateIndex M)) (Q : Finset ℕ) (hQ : Q ⊆ auxiliaryPrimes B)
    (R : Q → I.powerset) : ℝ :=
  finiteProductMass (fun p : Q => @outsideCandidatePrimeMass M I p.val
    ⟨auxiliaryPrimes_prime B p.val (hQ p.property)⟩) R

open Classical in
theorem outsideCandidateProduct_l1 {B M : ℕ} (I : Finset (BlockCandidateIndex M))
    (Q : Finset ℕ) (hQ : Q ⊆ auxiliaryPrimes B)
    (hsize : ∀ p ∈ Q, M < p) (hhalf : ∀ p ∈ Q, 2*M ≤ p) :
    (∑ R, |outsideCandidateProductMass B I Q hQ R-
      bernoulliProductMass I (fun p : Q => fun _ => 1/(p.val : ℝ)) R|) ≤
      8*((I.card : ℝ)+(M : ℝ))^2*(∑ p ∈ auxiliaryPrimes B, 1/(p : ℝ)^2)+
        6*(I.card : ℝ)*(∑ p ∈ candidateDefectPrimes B I, 1/(p : ℝ)) := by
  let a := fun p : Q => @outsideCandidatePrimeMass M I p.val
    ⟨auxiliaryPrimes_prime B p.val (hQ p.property)⟩
  let b := fun p : Q => fun S : I.powerset => bernoulliSubsetMass I (fun _ => 1/(p.val : ℝ)) S.val
  have ha (p : Q) (S : I.powerset) : 0 ≤ a p S := by
    let : Fact p.val.Prime := ⟨auxiliaryPrimes_prime B p.val (hQ p.property)⟩
    exact outsideCandidatePrimeMass_nonneg I p.val S
  have haone (p : Q) : ∑ S, a p S = 1 := by
    let : Fact p.val.Prime := ⟨auxiliaryPrimes_prime B p.val (hQ p.property)⟩
    exact outsideCandidatePrimeMass_sum I p.val (hsize p.val p.property)
  have hb (p : Q) (S : I.powerset) : 0 ≤ b p S := by
    apply bernoulliSubsetMass_nonneg (mem_powerset.mp S.property)
    intro _ _
    have hp : (1 : ℝ) ≤ p.val := by
      exact_mod_cast (auxiliaryPrimes_prime B p.val (hQ p.property)).one_le
    exact ⟨by positivity,(div_le_one (by linarith)).mpr hp⟩
  have hbone (p : Q) : ∑ S, b p S = 1 :=
    (sum_coe_sort _ _).trans (bernoulliSubsetMass_sum _ _)
  have hlocal (p : Q) : (∑ S, |a p S-b p S|) ≤
      8*((I.card : ℝ)+(M : ℝ))^2/(p.val : ℝ)^2+
        if p.val ∈ candidateDefectPrimes B I then 6*(I.card : ℝ)/(p.val : ℝ) else 0 :=
    @outsideCandidatePrimeMass_l1 B M p.val
      ⟨auxiliaryPrimes_prime B p.val (hQ p.property)⟩ I (hQ p.property)
      (hsize p.val p.property) (hhalf p.val p.property)
  have hsq : (∑ p ∈ Q, 1/(p : ℝ)^2) ≤ ∑ p ∈ auxiliaryPrimes B, 1/(p : ℝ)^2 :=
    sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => by positivity)
  have hdef : Q.filter (fun p => p ∈ candidateDefectPrimes B I) ⊆ candidateDefectPrimes B I :=
    fun _ hp => (mem_filter.mp hp).2
  have hrec : (∑ p ∈ Q, if p ∈ candidateDefectPrimes B I then 1/(p : ℝ) else 0) ≤
      ∑ p ∈ candidateDefectPrimes B I, 1/(p : ℝ) := by
    rw [← sum_filter]
    exact sum_le_sum_of_subset_of_nonneg hdef (fun _ _ _ => by positivity)
  calc
    _ ≤ ∑ p : Q, ∑ S, |a p S-b p S| := finiteProductMass_l1_le a b ha hb haone hbone
    _ ≤ ∑ p : Q, (8*((I.card : ℝ)+(M : ℝ))^2/(p.val : ℝ)^2+
        if p.val ∈ candidateDefectPrimes B I then 6*(I.card : ℝ)/(p.val : ℝ) else 0) :=
      sum_le_sum (fun p _ => hlocal p)
    _ = 8*((I.card : ℝ)+(M : ℝ))^2*(∑ p ∈ Q, 1/(p : ℝ)^2)+
        6*(I.card : ℝ)*(∑ p ∈ Q, if p ∈ candidateDefectPrimes B I then 1/(p : ℝ) else 0) := by
      rw [show (∑ p : Q, (8*((I.card : ℝ)+(M : ℝ))^2/(p.val : ℝ)^2+
        if p.val ∈ candidateDefectPrimes B I then 6*(I.card : ℝ)/(p.val : ℝ) else 0)) =
        ∑ p ∈ Q, (8*((I.card : ℝ)+(M : ℝ))^2/(p : ℝ)^2+
        if p ∈ candidateDefectPrimes B I then 6*(I.card : ℝ)/(p : ℝ) else 0) from
          sum_coe_sort Q (fun p : ℕ => (8*((I.card : ℝ)+(M : ℝ))^2/(p : ℝ)^2+
            if p ∈ candidateDefectPrimes B I then 6*(I.card : ℝ)/(p : ℝ) else 0))]
      simp only [sum_add_distrib,mul_sum]
      apply congrArg₂ (· + ·)
      · apply sum_congr rfl; intro p _; ring
      · apply sum_congr rfl; intro p _; split_ifs <;> ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hsq (by positivity))
      (mul_le_mul_of_nonneg_left hrec (by positivity))

end JointDickman

end OAI
