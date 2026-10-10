import OAI.NumberTheory.JointDickman.Amplification.GraphEdgeMeanBound
import OAI.NumberTheory.JointDickman.Counting.CoefficientTripleBound

namespace OAI

/-! # Summing the harmonic coefficient mass for a fixed positive lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def graphCoefficientHarmonicTerm (B j : ℕ) (bc : ℕ × ℕ) : ℝ :=
  (coefficientWeight B bc.1 * coefficientWeight B bc.2 *
    coefficientWeight B (bc.1+j*bc.2)) / ((bc.1 : ℝ)*(bc.1+j*bc.2))

theorem graphCoefficientHarmonicTerm_nonneg (B j : ℕ) (bc : ℕ × ℕ) :
    0 ≤ graphCoefficientHarmonicTerm B j bc :=
  div_nonneg (mul_nonneg (mul_nonneg (coefficientWeight_nonneg B bc.1)
    (coefficientWeight_nonneg B bc.2)) (coefficientWeight_nonneg B (bc.1+j*bc.2)))
    (by positivity)

theorem graphCoefficientHarmonic_box
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T k j : ℕ, 0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      k ∈ Ico B (4*B) → j ≠ 0 →
      (∑ bc ∈ coefficientDyadicBox T k, graphCoefficientHarmonicTerm B j bc) ≤
        (3*C/(T : ℝ))*singularFactor 24 j := by
  obtain ⟨C,hC,hbound⟩ := coefficient_three_form_bound hFord hM (δ := 1/2) (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound, coefficientDyadicBox_scales] with B hB hscale
  intro T k j hT hTsize hk hj
  let q : ℕ := 2^k
  have hq : 0 < q := by dsimp [q]; positivity
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hlow : Real.exp ((1/2 : ℝ)*B) ≤ (q : ℝ) := (hscale T k hTsize hk).1
  have huv : T*q ≤ 4*T*q := by nlinarith
  have hwx : q ≤ 2*q := by omega
  have hlong₁ : Real.exp ((1/2 : ℝ)*B) ≤ (4*T*q : ℕ) - (T*q : ℝ) := by
    push_cast
    have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hlong₂ : Real.exp ((1/2 : ℝ)*B) ≤ (2*q : ℕ) - (q : ℝ) := by
    push_cast
    linarith
  have hb := hB j (T*q) (4*T*q) q (2*q) hj huv hwx (by simpa only [Nat.cast_mul] using hlong₁) hlong₂
  have hD : (0 : ℝ) < (T*q : ℝ)^2 := sq_pos_of_pos (mul_pos hTr hqr)
  calc
    _ ≤ (∑ bc ∈ coefficientDyadicBox T k,
        coefficientWeight B bc.1 * coefficientWeight B bc.2 *
          coefficientWeight B (bc.1+j*bc.2)) / (T*q : ℝ)^2 := by
      rw [sum_div]
      apply sum_le_sum
      intro bc hbc
      have hbc' := mem_Ico.mp (mem_product.mp hbc).1
      have hlo : (T*q : ℝ) ≤ bc.1 := by exact_mod_cast hbc'.1
      have hhi : (T*q : ℝ) ≤ (bc.1+j*bc.2 : ℕ) := by
        exact_mod_cast (hbc'.1.trans (Nat.le_add_right _ _))
      have hden : (T*q : ℝ)^2 ≤ (bc.1 : ℝ)*(bc.1+j*bc.2 : ℕ) := by
        simpa only [pow_two] using mul_le_mul hlo hhi (mul_pos hTr hqr).le
          (by positivity : (0 : ℝ) ≤ bc.1)
      simp only [Nat.cast_add, Nat.cast_mul] at hden
      exact div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg (coefficientWeight_nonneg B bc.1)
          (coefficientWeight_nonneg B bc.2)) (coefficientWeight_nonneg B (bc.1+j*bc.2))) hD hden
    _ ≤ (C*((4*T*q : ℕ)-(T*q : ℝ))*((2*q : ℕ)-(q : ℝ))*singularFactor 24 j) /
        (T*q : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ hD.le
      simpa only [coefficientDyadicBox, q, sum_product, Nat.cast_mul, Nat.cast_ofNat] using hb
    _ = (3*C/(T : ℝ))*singularFactor 24 j := by
      push_cast
      field_simp
      ring

/-- The O(B) dyadic boxes cost only a constant per box after the harmonic
denominator is included. This is the coefficient sum in the edge mass. -/
theorem graphCoefficientHarmonic_mass
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T j : ℕ, 0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      (∑ bc ∈ amplificationCoefficientPairs B T, graphCoefficientHarmonicTerm B j bc) ≤
        C*(B : ℝ)/(T : ℝ)*singularFactor 24 j := by
  obtain ⟨C,hC,hbox⟩ := graphCoefficientHarmonic_box hFord hM
  refine ⟨9*C, by positivity, ?_⟩
  filter_upwards [hbox] with B hB
  intro T j hT hTsize hj
  calc
    _ ≤ ∑ bc ∈ coefficientDyadicCover B T, graphCoefficientHarmonicTerm B j bc :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun bc _ _ => graphCoefficientHarmonicTerm_nonneg B j bc)
    _ = ∑ k ∈ Ico B (4*B),
        ∑ bc ∈ coefficientDyadicBox T k, graphCoefficientHarmonicTerm B j bc := by
      apply sum_biUnion
      intro k hk l hl hkl
      exact coefficientDyadicBox_disjoint T hkl
    _ ≤ ∑ _k ∈ Ico B (4*B), (3*C/(T : ℝ))*singularFactor 24 j :=
      sum_le_sum (fun k hk => hB T k j hT hTsize hk hj)
    _ = (9*C)*(B : ℝ)/(T : ℝ)*singularFactor 24 j := by
      have hcard : (Ico B (4*B)).card = 3*B := by simp; omega
      rw [sum_const, hcard, nsmul_eq_mul]
      push_cast
      ring

end JointDickman

end OAI
