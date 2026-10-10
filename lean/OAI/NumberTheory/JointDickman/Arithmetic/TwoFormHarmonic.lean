import OAI.NumberTheory.JointDickman.Counting.CoefficientPairBound

namespace OAI

/-! # Harmonic form of the fixed-endpoint coefficient bound -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem two_form_harmonic_box
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) (κ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T q j b : ℕ,
      0 < T → Real.exp (δ*B) ≤ (q : ℝ) → T*q ≤ b → j ≠ 0 →
      (b : ℝ) ≤ Real.exp (κ*B) →
      Disjoint b.primeFactors (Nat.primesLE (auxiliaryCutoff B)) →
      (∑ c ∈ Ico q (4*q),
        (coefficientWeight B c*coefficientWeight B (b+j*c))/(b+j*c : ℕ)) ≤
          K/(T : ℝ)*singularFactor 24 j := by
  obtain ⟨K,hK,hbound⟩ := coefficient_two_form_bound hFord hM hδ κ
  refine ⟨3*K,by positivity,?_⟩
  filter_upwards [hbound] with B hB
  intro T q j b hT hq hTb hj hbsize hbrough
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hqr : (0 : ℝ) < q := lt_of_lt_of_le (Real.exp_pos _) hq
  have hq0 : 0 < q := by exact_mod_cast hqr
  have hb : b ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.mul_pos hT hq0) hTb)
  have hlen : Real.exp (δ*B) ≤ (4*q : ℕ)-(q : ℝ) := by
    push_cast
    linarith
  have hsum := hB j b q (4*q) hj hb hbsize hbrough (by omega) hlen
  have hden0 : (0 : ℝ) < (T : ℝ)*q := mul_pos hTr hqr
  calc
    _ ≤ (∑ c ∈ Ico q (4*q), coefficientWeight B c*coefficientWeight B (b+j*c))/((T : ℝ)*q) := by
      rw [sum_div]
      apply sum_le_sum
      intro c _
      have hden : (T : ℝ)*q ≤ (b+j*c : ℕ) := by
        exact_mod_cast hTb.trans (Nat.le_add_right b (j*c))
      exact div_le_div_of_nonneg_left
        (mul_nonneg (coefficientWeight_nonneg _ _) (coefficientWeight_nonneg _ _)) hden0 hden
    _ ≤ (K*((4*q : ℕ)-(q : ℝ))*singularFactor 24 j)/((T : ℝ)*q) :=
      div_le_div_of_nonneg_right hsum hden0.le
    _ = _ := by
      push_cast
      field_simp
      ring

end JointDickman

end OAI
