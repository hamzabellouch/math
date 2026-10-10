import OAI.NumberTheory.JointDickman.Amplification.CandidateMultiplicityBound
import OAI.NumberTheory.JointDickman.Probability.ArithmeticSplitWeights

namespace OAI

/-! # Exact first-representation mass with both regularity tests -/

namespace JointDickman
open Finset Classical

/-- The forced coefficient and tilted normalization together give exactly
the half-prime subset law, scaled by B. -/
theorem coefficient_tilt_mass {B : ℕ} (hB : 1 < B) {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) :
    coefficientWeight B (∏ p ∈ A, p)*(remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ)) =
      (B : ℝ)*bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A := by
  rw [coefficientWeight_primeProduct hA]
  have hR := auxiliaryRatio_pos hB
  have hs : (auxiliaryRatio B)^(1/2 : ℝ)*(auxiliaryRatio B)^(1/2 : ℝ) = auxiliaryRatio B := by
    rw [← Real.rpow_add hR]
    norm_num
  have hp : (1/2 : ℝ)^A.card/(∏ p ∈ A, p : ℕ) = ∏ p ∈ A, (1/2 : ℝ)/p := by
    rw [prod_div_distrib,prod_const,Nat.cast_prod]
  unfold residueBaseWeight remainderTiltNormalizer bernoulliSubsetMass primeNormalizer
  calc
    _ = (auxiliaryRatio B^(1/2 : ℝ)*auxiliaryRatio B^(1/2 : ℝ))*
        Real.log (auxiliaryCutoff B)*((1/2 : ℝ)^A.card/(∏ p ∈ A, p : ℕ))*
        ∏ p ∈ auxiliaryPrimes B \ A, (1-(1/2 : ℝ)/p) := by ring
    _ = _ := by rw [hs,auxiliaryRatio_mul_log hB,hp]; ring

/-- Regularity is kept inside the changed probability measure. In
particular, this identity makes no division by a regularity probability. -/
theorem regular_pair_change_of_measure {B L : ℕ} {τ C : ℝ} {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
      if A ⊆ S ∧ D ⊆ R then
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
        regularResidueWeight B L τ C (S \ A)*regularResidueWeight B L τ C (R \ D)*F S R
      else 0) =
      (remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ))*
      (remainderTiltNormalizer B D/(∏ p ∈ D, p : ℕ))*
      regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D
        (fun V => F (A ∪ U) (D ∪ V))) := by
  let G := fun S R => if RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D)
    then F S R else 0
  have hpoint (S R : Finset ℕ) :
      regularResidueWeight B L τ C (S \ A)*regularResidueWeight B L τ C (R \ D)*F S R =
        residueBaseWeight B (S \ A)*residueBaseWeight B (R \ D)*G S R := by
    dsimp only [G]
    unfold regularResidueWeight
    split_ifs <;> simp_all
  have hpoint2 (S R : Finset ℕ) :
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
        regularResidueWeight B L τ C (S \ A)*regularResidueWeight B L τ C (R \ D)*F S R =
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
        residueBaseWeight B (S \ A)*residueBaseWeight B (R \ D)*G S R := by
    have hh := congrArg (fun x =>
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*x) (hpoint S R)
    convert hh using 1 <;> ring
  simp_rw [hpoint2]
  rw [weighted_endpoint_pair_change_of_measure hA hD G]
  congr 1
  unfold regularTiltAverage
  apply sum_congr rfl
  intro U hU
  have hu : (A ∪ U) \ A = U := by
    ext p
    have hh : p ∈ U → p ∉ A := fun hp => (mem_sdiff.mp (mem_powerset.mp hU hp)).2
    simp only [mem_sdiff,mem_union]
    tauto
  have hpoint' (V : Finset ℕ) (hV : V ∈ (auxiliaryPrimes B \ D).powerset) :
      G (A ∪ U) (D ∪ V) = if RegularPrimeSet B L τ C U then
        if RegularPrimeSet B L τ C V then F (A ∪ U) (D ∪ V) else 0 else 0 := by
    have hv : (D ∪ V) \ D = V := by
      ext p
      have hh : p ∈ V → p ∉ D := fun hp => (mem_sdiff.mp (mem_powerset.mp hV hp)).2
      simp only [mem_sdiff,mem_union]
      tauto
    simp only [G,hu,hv]
    split_ifs <;> simp_all
  by_cases hr : RegularPrimeSet B L τ C U
  · simp only [hr,ite_true]
    rw [mul_sum]
    apply sum_congr rfl
    intro V hV
    rw [hpoint' V hV,ite_eq_left hr]
    ring
  · rw [ite_eq_right hr,mul_zero]
    apply sum_eq_zero
    intro V hV
    rw [hpoint' V hV,ite_eq_right hr,mul_zero]

end JointDickman

end OAI
