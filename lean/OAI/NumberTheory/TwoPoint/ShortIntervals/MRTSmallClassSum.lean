import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogClassBounds

namespace OAI

/-! The full small-class contribution, with all actual prime-bin and
extraction costs summed independently of the number of bands. -/

namespace TwoPointCorrelations

open Finset MeasureTheory Set
open scoped Classical

lemma mrt_sum_range_succ (f : ℕ → ℝ) (J : ℕ) :
    (∑ r ∈ range J, f (r+1)) = ∑ j ∈ Finset.Icc 1 J, f j := by
  rw [range_eq_Ico, sum_Ico_add' f 0 J 1]
  simp only [Nat.zero_add, Finset.Ico_add_one_right_eq_Icc]

lemma mrt_shifted_inverse_square_sum (J : ℕ) :
    (∑ r ∈ range J, (((r:ℝ)+1)^2)⁻¹) ≤ 2 := by
  have he : Finset.Icc 1 J = Finset.Ioo 0 (J+1) := by ext j; simp; omega
  have hs := mrt_sum_range_succ (fun j => ((j:ℝ)^2)⁻¹) J
  simp only [Nat.cast_add, Nat.cast_one] at hs
  rw [hs, he]
  simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 (J+1)

theorem mrt_small_log_class_sum (V : ℕ → Finset ℕ) (J : ℕ)
    (hprime : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j, p.Prime)
    (hdis : Set.PairwiseDisjoint (Finset.Icc 1 J : Set ℕ) V)
    {P Q η : ℝ} (hP0 : 0 < P) (hQ0 : 0 < Q)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q) (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η)
    (hrange : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j,
      mrtBandLower P Q j ≤ (p:ℝ) ∧ (p:ℝ) ≤ mrtBandUpper Q j)
    {N : ℕ} (hN : 0 < N) (hsize : 2*Q ≤ (N:ℝ))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) :
    (∑ r ∈ range J, ∫ t in mrtFirstLogClass V F P Q η r T,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
      33792*Real.exp 1*(T/N+1)*(mrtBaseResolution P Q η)⁻¹ +
      1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹ +
      2*(T/N+1)*P⁻¹ := by
  let C := 2816*Real.exp 1*(T/N+1)
  let D := (T/N+1)*P⁻¹
  let B := 1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have herr : (∑ r ∈ range J, mrtLogExtractionError V P Q η (r+1)) ≤
      12*(mrtBaseResolution P Q η)⁻¹ := by
    rw [mrt_sum_range_succ]
    exact mrt_prime_extraction_error_sum V J hP0 hP hQ hη.le hH
      (fun j hj p hp => (hrange j hj p hp).1)
  have hone : (∑ r ∈ range J, if r = 0 then B else 0) ≤ B := by
    rw [sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact hB
  calc
    _ ≤ ∑ r ∈ range J, (C*mrtLogExtractionError V P Q η (r+1) +
        (if r = 0 then B else 0) + D*(((r:ℝ)+1)^2)⁻¹) := by
      apply sum_le_sum
      intro r hr
      exact mrt_log_class_energy V J hprime hdis hP0 hQ0 hP hQ hPQ hη hη'
        hbudget hH hrange hN hsize F hF hFb hT hr
    _ = C*(∑ r ∈ range J, mrtLogExtractionError V P Q η (r+1)) +
        (∑ r ∈ range J, if r = 0 then B else 0) +
        D*(∑ r ∈ range J, (((r:ℝ)+1)^2)⁻¹) := by
      simp only [sum_add_distrib, mul_sum]
    _ ≤ C*(12*(mrtBaseResolution P Q η)⁻¹) + B + D*2 :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left herr hC) hone)
        (mul_le_mul_of_nonneg_left (mrt_shifted_inverse_square_sum J) hD)
    _ = _ := by dsimp [C, D, B]; ring

theorem mrt_log_energy_partition_bound (V : ℕ → Finset ℕ) (J : ℕ)
    (hprime : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j, p.Prime)
    (hdis : Set.PairwiseDisjoint (Finset.Icc 1 J : Set ℕ) V)
    {P Q η : ℝ} (hP0 : 0 < P) (hQ0 : 0 < Q)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q) (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η)
    (hrange : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j,
      mrtBandLower P Q j ≤ (p:ℝ) ∧ (p:ℝ) ≤ mrtBandUpper Q j)
    {N : ℕ} (hN : 0 < N) (hsize : 2*Q ≤ (N:ℝ))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
      (∫ t in Ioc (-T) T ∩ mrtNoSmallBand (mrtLogFamilyBins P Q η)
        (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) J,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) +
      (33792*Real.exp 1*(T/N+1)*(mrtBaseResolution P Q η)⁻¹ +
      1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹ +
      2*(T/N+1)*P⁻¹) := by
  rw [mrt_log_partition_integral V J F P Q η hT.le]
  exact add_le_add le_rfl (mrt_small_log_class_sum V J hprime hdis hP0 hQ0 hP hQ hPQ
    hη hη' hbudget hH hrange hN hsize F hF hFb hT)

end TwoPointCorrelations

end OAI
