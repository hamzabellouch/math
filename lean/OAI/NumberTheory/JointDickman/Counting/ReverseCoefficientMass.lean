import OAI.NumberTheory.JointDickman.Counting.CoefficientSubtraction
import OAI.NumberTheory.JointDickman.Counting.CoefficientDomination

namespace OAI

/-! # Harmonic coefficient mass with the upper endpoint fixed -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem two_form_sub_harmonic_box
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) (κ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T q j b : ℕ,
      0 < T → Real.exp (δ*B) ≤ (q : ℝ) → T*q ≤ b → j ≠ 0 →
      (b : ℝ) ≤ Real.exp (κ*B) →
      Disjoint b.primeFactors (Nat.primesLE (auxiliaryCutoff B)) →
      (∑ c ∈ Ico q (4*q), if T*q ≤ b-j*c then
        (coefficientWeight B c*coefficientWeight B (b-j*c))/(b-j*c : ℕ) else 0) ≤
          K/(T : ℝ)*singularFactor 24 j := by
  obtain ⟨K,hK,hbound⟩ := coefficient_two_form_sub_bound hFord hM hδ κ
  refine ⟨3*K,by positivity,?_⟩
  filter_upwards [hbound] with B hB
  intro T q j b hT hq hTb hj hbsize hbrough
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hqr : (0 : ℝ) < q := lt_of_lt_of_le (Real.exp_pos _) hq
  have hq0 : 0 < q := by exact_mod_cast hqr
  have hb : b ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.mul_pos hT hq0) hTb)
  have hlen : Real.exp (δ*B) ≤ (4*q : ℕ)-(q : ℝ) := by push_cast; linarith
  have hsum := hB j b q (4*q) hj hb hbsize hbrough (by omega) hlen
  have hden0 : (0 : ℝ) < (T : ℝ)*q := mul_pos hTr hqr
  calc
    _ ≤ (∑ c ∈ Ico q (4*q), coefficientWeight B c*coefficientWeight B (b-j*c))/((T : ℝ)*q) := by
      rw [sum_div]
      apply sum_le_sum
      intro c _
      split_ifs with hc
      · have hden : (T : ℝ)*q ≤ (b-j*c : ℕ) := by exact_mod_cast hc
        exact div_le_div_of_nonneg_left
          (mul_nonneg (coefficientWeight_nonneg _ _) (coefficientWeight_nonneg _ _)) hden0 hden
      · exact div_nonneg (mul_nonneg (coefficientWeight_nonneg _ _)
          (coefficientWeight_nonneg _ _)) hden0.le
    _ ≤ (K*((4*q : ℕ)-(q : ℝ))*singularFactor 24 j)/((T : ℝ)*q) :=
      div_le_div_of_nonneg_right hsum hden0.le
    _ = _ := by push_cast; field_simp; ring

noncomputable def reverseCoefficientMass (B T b j q : ℕ) : ℝ :=
  ∑ c ∈ Ico q (4*q), if T*q ≤ b-j*c ∧ (b-j*c : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) then
    primeProductMass (auxiliaryPrimes B) (1/2) (b-j*c)*coefficientWeight B c else 0

theorem reverseCoefficientMass_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) (κ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T q j b : ℕ,
      0 < T → Real.exp (δ*B) ≤ (q : ℝ) → T*q ≤ b → j ≠ 0 →
      (b : ℝ) ≤ Real.exp (κ*B) →
      Disjoint b.primeFactors (Nat.primesLE (auxiliaryCutoff B)) →
      reverseCoefficientMass B T b j q ≤ K/((B : ℝ)*T)*singularFactor 24 j := by
  obtain ⟨K,hK,harmonic⟩ := two_form_sub_harmonic_box hFord hM hδ κ
  obtain ⟨D,hD,hdom⟩ := primeProductMass_coefficient_domination hM
  refine ⟨D*K,by positivity,?_⟩
  filter_upwards [harmonic,hdom,eventually_gt_atTop 0] with B hB hmass hB0
  intro T q j b hT hq hTb hj hbsize hbrough
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB0
  have hq0 : 0 < q := by exact_mod_cast lt_of_lt_of_le (Real.exp_pos _) hq
  have hs := hB T q j b hT hq hTb hj hbsize hbrough
  have hpoint (c : ℕ) : (if T*q ≤ b-j*c ∧ (b-j*c : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) then
      primeProductMass (auxiliaryPrimes B) (1/2) (b-j*c)*coefficientWeight B c else 0) ≤
      D/(B : ℝ)*(if T*q ≤ b-j*c then
        coefficientWeight B c*coefficientWeight B (b-j*c)/(b-j*c : ℕ) else 0) := by
    by_cases hc : T*q ≤ b-j*c
    · by_cases ha : (b-j*c : ℕ) ≤ Real.exp ((16/5 : ℝ)*B)
      · simp only [hc,ha,and_self,ite_true]
        have hh := mul_le_mul_of_nonneg_right (hmass (b-j*c)
          (lt_of_lt_of_le (Nat.mul_pos hT hq0) hc) ha) (coefficientWeight_nonneg B c)
        convert hh using 1; ring
      · simp only [hc,ha,and_false,ite_false,ite_true]
        exact mul_nonneg (div_nonneg hD.le hBr.le)
          (div_nonneg (mul_nonneg (coefficientWeight_nonneg _ _) (coefficientWeight_nonneg _ _))
            (Nat.cast_nonneg _))
    · simp only [hc,false_and,ite_false,mul_zero,le_refl]
  calc
    _ ≤ ∑ c ∈ Ico q (4*q), D/(B : ℝ)*(if T*q ≤ b-j*c then
        coefficientWeight B c*coefficientWeight B (b-j*c)/(b-j*c : ℕ) else 0) :=
      sum_le_sum (fun c _ => hpoint c)
    _ = D/(B : ℝ)*(∑ c ∈ Ico q (4*q), if T*q ≤ b-j*c then
        coefficientWeight B c*coefficientWeight B (b-j*c)/(b-j*c : ℕ) else 0) := (mul_sum _ _ _).symm
    _ ≤ D/(B : ℝ)*(K/(T : ℝ)*singularFactor 24 j) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg hD.le hBr.le)
    _ = _ := by ring

end JointDickman

end OAI
