import OAI.NumberTheory.JointDickman.Arithmetic.TwoFormHarmonic
import OAI.NumberTheory.JointDickman.Counting.CoefficientDomination

namespace OAI

/-! # The half-prime coefficient mass at a fixed first endpoint -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def endpointCoefficientMass (B b j q : ℕ) : ℝ :=
  ∑ c ∈ Ico q (4*q), if (b+j*c : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) then
    primeProductMass (auxiliaryPrimes B) (1/2) (b+j*c)*coefficientWeight B c else 0

/-- After averaging the second endpoint, each fixed first coefficient
costs O(Sigma(j)/(B T)); its fair-split prefactor later supplies B. -/
theorem endpointCoefficientMass_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) (κ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T q j b : ℕ,
      0 < T → Real.exp (δ*B) ≤ (q : ℝ) → T*q ≤ b → j ≠ 0 →
      (b : ℝ) ≤ Real.exp (κ*B) →
      Disjoint b.primeFactors (Nat.primesLE (auxiliaryCutoff B)) →
      endpointCoefficientMass B b j q ≤ K/((B : ℝ)*T)*singularFactor 24 j := by
  obtain ⟨K,hK,harmonic⟩ := two_form_harmonic_box hFord hM hδ κ
  obtain ⟨D,hD,hdom⟩ := primeProductMass_coefficient_domination hM
  refine ⟨D*K,by positivity,?_⟩
  filter_upwards [harmonic,hdom,eventually_gt_atTop 0] with B hB hmass hB0
  intro T q j b hT hq hTb hj hbsize hbrough
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB0
  have hqr : (0 : ℝ) < q := lt_of_lt_of_le (Real.exp_pos _) hq
  have hq0 : 0 < q := by exact_mod_cast hqr
  have hb : 0 < b := lt_of_lt_of_le (Nat.mul_pos hT hq0) hTb
  have hs := hB T q j b hT hq hTb hj hbsize hbrough
  have hpoint (c : ℕ) : (if (b+j*c : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) then
      primeProductMass (auxiliaryPrimes B) (1/2) (b+j*c)*coefficientWeight B c else 0) ≤
      D/(B : ℝ)*(coefficientWeight B c*coefficientWeight B (b+j*c)/(b+j*c : ℕ)) := by
    split_ifs with ha
    · have hh := mul_le_mul_of_nonneg_right (hmass (b+j*c)
        (lt_of_lt_of_le hb (Nat.le_add_right _ _)) ha) (coefficientWeight_nonneg B c)
      convert hh using 1; ring
    · exact mul_nonneg (div_nonneg hD.le hBr.le)
        (div_nonneg (mul_nonneg (coefficientWeight_nonneg B c) (coefficientWeight_nonneg B (b+j*c)))
          (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ c ∈ Ico q (4*q), D/(B : ℝ)*
        (coefficientWeight B c*coefficientWeight B (b+j*c)/(b+j*c : ℕ)) :=
      sum_le_sum (fun c _ => hpoint c)
    _ = D/(B : ℝ)*(∑ c ∈ Ico q (4*q),
        coefficientWeight B c*coefficientWeight B (b+j*c)/(b+j*c : ℕ)) := (mul_sum _ _ _).symm
    _ ≤ D/(B : ℝ)*(K/(T : ℝ)*singularFactor 24 j) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg hD.le hBr.le)
    _ = _ := by ring

end JointDickman

end OAI
