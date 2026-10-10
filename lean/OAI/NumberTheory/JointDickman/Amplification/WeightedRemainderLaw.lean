import OAI.NumberTheory.JointDickman.Arithmetic.RequiredPrimeSubset
import OAI.NumberTheory.JointDickman.Amplification.IndependentRootMean
import OAI.NumberTheory.JointDickman.Arithmetic.ConditionalPrimeParameters

namespace OAI

/-! # The exact measure obtained by weighting the first representation

After requiring a coefficient and weighting the remaining primes by one
half, the unforced indicators have probability 1/(2p-1). Regularity tests
remain inside the expectation and do not alter its normalization.
-/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem required_prime_mass_factor {P A S : Finset ℕ}
    (hA : A ⊆ S) (_hS : S ⊆ P) :
    bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S =
      (1/(∏ p ∈ A, p : ℕ))*
        bernoulliSubsetMass (P \ A) (fun p => 1/(p : ℝ)) (S \ A) := by
  have he : (P \ A) \ (S \ A) = P \ S := by
    ext p
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hp, ha⟩, hs⟩
      exact ⟨hp,fun h => hs ⟨h,ha⟩⟩
    · rintro ⟨hp,hs⟩
      exact ⟨⟨hp,fun h => hs (hA h)⟩,fun h => hs h.1⟩
  have hp : (∏ p ∈ A, 1/(p : ℝ)) = 1/(∏ p ∈ A, p : ℕ) := by
    simp only [one_div,prod_inv_distrib,Nat.cast_prod]
  unfold bernoulliSubsetMass
  rw [he,← prod_sdiff hA,← hp]
  ring

theorem half_weight_tilt (P R : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hR : R ⊆ P) :
    bernoulliSubsetMass P (fun p => 1/(p : ℝ)) R*(1/2 : ℝ)^R.card =
      primeNormalizer P (1/2)*
        bernoulliSubsetMass P (fun p => 1/(2*(p : ℝ)-1)) R := by
  have hs (p : ℕ) (hp : p ∈ P) :
      1/(p : ℝ)*(1/2) = (1-(1/2 : ℝ)/p)*(1/(2*(p : ℝ)-1)) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hd : (p : ℝ)*2-1 ≠ 0 := by linarith
    field_simp [hp0, hd]
  have hn (p : ℕ) (hp : p ∈ P) :
      1-1/(p : ℝ) = (1-(1/2 : ℝ)/p)*(1-1/(2*(p : ℝ)-1)) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hd : (p : ℝ)*2-1 ≠ 0 := by linarith
    field_simp [hp0, hd]
    ring
  have hsel : (∏ p ∈ R, 1/(p : ℝ)*(1/2)) =
      ∏ p ∈ R, (1-(1/2 : ℝ)/p)*(1/(2*(p : ℝ)-1)) :=
    prod_congr rfl (fun p hp => hs p (hR hp))
  have hnon : (∏ p ∈ P \ R, (1-1/(p : ℝ))) =
      ∏ p ∈ P \ R, (1-(1/2 : ℝ)/p)*(1-1/(2*(p : ℝ)-1)) :=
    prod_congr rfl (fun p hp => hn p (mem_sdiff.mp hp).1)
  unfold bernoulliSubsetMass primeNormalizer
  rw [← prod_sdiff hR (f := fun p : ℕ => 1-(1/2 : ℝ)/p)]
  rw [prod_mul_distrib,prod_const] at hsel
  rw [mul_right_comm, hsel,hnon,prod_mul_distrib,prod_mul_distrib]
  ring

noncomputable def remainderTiltNormalizer (B : ℕ) (A : Finset ℕ) : ℝ :=
  auxiliaryRatio B^(1/2 : ℝ)*primeNormalizer (auxiliaryPrimes B \ A) (1/2)

theorem weighted_required_prime_mass {B : ℕ} {A S : Finset ℕ}
    (hA : A ⊆ S) (hS : S ⊆ auxiliaryPrimes B) :
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        residueBaseWeight B (S \ A) =
      (remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ))*
        bernoulliSubsetMass (auxiliaryPrimes B \ A)
          (fun p => 1/(2*(p : ℝ)-1)) (S \ A) := by
  rw [required_prime_mass_factor hA hS]
  have hR : S \ A ⊆ auxiliaryPrimes B \ A := sdiff_subset_sdiff hS subset_rfl
  have ht := half_weight_tilt (auxiliaryPrimes B \ A) (S \ A)
    (fun p hp => auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1) hR
  unfold residueBaseWeight remainderTiltNormalizer
  calc
    _ = auxiliaryRatio B^(1/2 : ℝ)/(∏ p ∈ A, p : ℕ)*
        (bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(p : ℝ)) (S \ A)*
          (1/2 : ℝ)^(S \ A).card) := by ring
    _ = _ := by rw [ht]; ring

/-- An arbitrary regularity or multiplicity test stays inside the new law. -/
theorem weighted_remainder_change_of_measure {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (F : Finset ℕ → ℝ) :
    (∑ S ∈ (auxiliaryPrimes B).powerset, if A ⊆ S then
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        residueBaseWeight B (S \ A)*F (S \ A) else 0) =
      remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ)*
        ∑ R ∈ (auxiliaryPrimes B \ A).powerset,
          bernoulliSubsetMass (auxiliaryPrimes B \ A)
            (fun p => 1/(2*(p : ℝ)-1)) R*F R := by
  rw [← sum_filter,mul_sum]
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
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  · intro S hS
    rw [weighted_required_prime_mass (mem_filter.mp hS).2
      (mem_powerset.mp (mem_filter.mp hS).1)]
    ring

end JointDickman

end OAI
