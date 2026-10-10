import OAI.NumberTheory.JointDickman.Counting.CountingCoefficientRegularity
import OAI.NumberTheory.JointDickman.Counting.TermCoefficientBound

namespace OAI

/-! # Regularity of the lag coefficients after division by the lag -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem normalized_coefficient_difference {T η x y a b A L : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hx : η*T ≤ x) (hy : η*T ≤ y)
    (hb : |b| ≤ A)
    (hab : |a-b| ≤ L*|x-y|/T) :
    |(T/x)*a-(T/y)*b| ≤ (L/η+A/η^2)*|x-y|/T := by
  have hx0 : 0 < x := (mul_pos hη hT).trans_le hx
  have ht : |T/x| ≤ 1/η := by
    rw [abs_of_pos (div_pos hT hx0)]
    convert div_le_div_of_nonneg_left hT.le (mul_pos hη hT) hx using 1; field_simp
  have hh := reciprocal_lag_difference hT hη hx hy
  calc
    _ = |(T/x)*(a-b)+(T/x-T/y)*b| := by congr 1; ring
    _ ≤ |(T/x)*(a-b)|+|(T/x-T/y)*b| := abs_add_le _ _
    _ = |T/x| *|a-b|+|T/x-T/y| *|b| := by rw [abs_mul,abs_mul]
    _ ≤ (1/η)*(L*|x-y|/T)+(|x-y|/(η^2*T))*A := by
      exact add_le_add (mul_le_mul ht hab (abs_nonneg _) (by positivity))
        (mul_le_mul hh hb (abs_nonneg _) (by positivity))
    _ = _ := by ring

theorem countingTermCoefficient_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T σ : ℝ),
      1 ≤ T → Real.log T ≤ (B : ℝ)/10 → |σ| ≤ 3 → ∀ a b : Fin m,
      |countingTermCoefficient P d m B j c H T σ a b| ≤ A := by
  obtain ⟨A,hA,hbound⟩ := weightedTermCoefficient_bounded hM hMP P d hm c hc H
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨A,hA,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 30] with B hbound hB
  intro j T σ hT hlog hσ a b
  apply hbound j T _
  · intro k hk
    exact (((dyadic_scale_window hB hT hlog).2.1 k hk).2).1
  · exact fun _ _ => hσ
  · intro k _
    rw [abs_of_nonneg (amplificationBump_bounds _).1]
    exact (amplificationBump_bounds _).2

theorem counting_normalized_coefficient_regular
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ A L : ℝ, 0 ≤ A ∧ 0 ≤ L ∧ ∀ᶠ B : ℕ in atTop, ∀ (j k : ℕ) (T σ : ℝ),
      1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j → η*T ≤ k → |σ| ≤ 3 →
      ∀ a b : Fin m,
        |(T/j)*countingTermCoefficient P d m B j c H T σ a b| ≤ A ∧
        |(T/j)*countingTermCoefficient P d m B j c H T σ a b-
          (T/k)*countingTermCoefficient P d m B k c H T σ a b| ≤ L*|(j : ℝ)-k|/T := by
  obtain ⟨A,hA,hbound⟩ := countingTermCoefficient_bounded hM hMP P d hm c hc H
  obtain ⟨L,hL,hreg⟩ := countingTermCoefficient_regular hM hMP P d hm c hc H hη
  refine ⟨A/η,L/η+A/η^2,by positivity,by positivity,?_⟩
  filter_upwards [hbound,hreg] with B hbound hreg
  intro j k T σ hT hlog hj hk hσ a b
  have hT0 : 0 < T := by linarith
  have hj0 : (0 : ℝ) < j := (mul_pos hη hT0).trans_le hj
  have hratio : T/(j : ℝ) ≤ 1/η := by
    convert div_le_div_of_nonneg_left hT0.le (mul_pos hη hT0) hj using 1; field_simp
  constructor
  · rw [abs_mul,abs_of_pos (div_pos hT0 hj0)]
    exact (mul_le_mul hratio (hbound j T σ hT hlog hσ a b) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  · apply normalized_coefficient_difference hT0 hη hj hk (hbound k T σ hT hlog hσ a b)
    simpa [mul_div_assoc] using hreg j k T σ σ hT hlog hj hk hσ hσ a b

end JointDickman

end OAI
