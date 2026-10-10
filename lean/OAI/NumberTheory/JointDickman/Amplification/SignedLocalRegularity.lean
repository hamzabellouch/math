import OAI.NumberTheory.JointDickman.Amplification.SignedRegularityLoss
import OAI.NumberTheory.JointDickman.Probability.SignedChannelMass

namespace OAI

/-! # Local regularity loss for the actual signed endpoint weights -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def signedLocalRegularityError (B L j : ℕ) (τ C : ℝ)
    (I J : Finset ℕ) (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (W : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ I, ∑ b ∈ I, ∑ c ∈ J,
    if a = b+j*c ∧ ¬ coefficientTripleRegular B L τ C a b c then
      |(B : ℝ)*signedSplitProductMass (auxiliaryPrimes B)
          (subsetSiteTest (auxiliaryPrimes B) g) a*
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
        coefficientWeight B c*W a b c| else 0

open Classical in
theorem signed_local_regularity_domination
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ L j : ℕ, ∀ τ C : ℝ,
      ∀ X : ℝ, 0 < X → ∀ I J : Finset ℕ,
      (∀ n ∈ I, X ≤ n ∧ (n : ℝ) ≤ Real.exp ((16/5 : ℝ)*B)) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      ∀ W : ℕ → ℕ → ℕ → ℝ, (∀ a ∈ I, ∀ b ∈ I, ∀ c ∈ J, |W a b c| ≤ 1) →
      signedLocalRegularityError B L j τ C I J g h W ≤
        (K^2/((B : ℝ)*X^2))*signedDiscardedCoefficientMass B L τ C j I J := by
  obtain ⟨K,hK,hbound⟩ := signedSplitProductMass_coefficient_bound hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_gt_atTop 0] with B hb hB
  intro L j τ C X hX I J hI g h hg hh W hW
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hBX : 0 < (B : ℝ)*X := mul_pos hBr hX
  have htest (f : (auxiliaryPrimes B → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1)
      (n : ℕ) (hn : n ∈ I) :
      |signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) f) n| ≤
        (K/((B : ℝ)*X))*coefficientWeight B n := by
    have hnpos : 0 < n := by exact_mod_cast (hX.trans_le (hI n hn).1)
    have hh := hb (subsetSiteTest (auxiliaryPrimes B) f) (fun S _ => hf _) n hnpos (hI n hn).2
    calc
      _ ≤ K*coefficientWeight B n/((B : ℝ)*n) := hh
      _ ≤ K*coefficientWeight B n/((B : ℝ)*X) :=
        div_le_div_of_nonneg_left (mul_nonneg hK.le (coefficientWeight_nonneg _ _)) hBX
          (mul_le_mul_of_nonneg_left (hI n hn).1 hBr.le)
      _ = _ := by ring
  unfold signedLocalRegularityError signedDiscardedCoefficientMass
  rw [mul_sum]
  apply sum_le_sum
  intro a ha
  rw [mul_sum]
  apply sum_le_sum
  intro b hbI
  rw [mul_sum]
  apply sum_le_sum
  intro c hc
  by_cases hrel : a = b+j*c
  · by_cases hreg : coefficientTripleRegular B L τ C a b c
    · simp only [hreg,not_true_eq_false,and_false,ite_false,discardedRelationWeight,
        ite_true,mul_zero]
      exact le_rfl
    · rw [ite_eq_left ⟨hrel,hreg⟩,discardedRelationWeight,ite_eq_right hreg,
        coefficientRelationWeight_nat,ite_eq_left hrel]
      have hga := htest g hg a ha
      have hhb := htest h hh b hbI
      have hA := coefficientWeight_nonneg B a
      have hD := coefficientWeight_nonneg B b
      have hC := coefficientWeight_nonneg B c
      have hpair := mul_le_mul hga hhb (abs_nonneg _) (by positivity)
      rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_of_pos hBr,abs_of_nonneg hC]
      calc
        _ ≤ (B : ℝ)*((K/((B : ℝ)*X))*coefficientWeight B a*
            ((K/((B : ℝ)*X))*coefficientWeight B b))*coefficientWeight B c*1 := by
          apply mul_le_mul
          · simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpair hBr.le) hC
          · exact hW a ha b hbI c hc
          · exact abs_nonneg _
          · positivity
        _ = _ := by
          unfold tripleCoefficientWeight
          rw [← hrel]
          field_simp
  · have hz : coefficientRelationWeight B (j : ℤ) a b c = 0 := by
      rw [coefficientRelationWeight_nat,ite_eq_right hrel]
    simp [hrel,discardedRelationWeight,hz]

end JointDickman

end OAI
