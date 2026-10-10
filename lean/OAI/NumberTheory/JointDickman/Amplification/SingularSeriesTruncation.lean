import OAI.NumberTheory.JointDickman.Amplification.ProjectedMajorIntegral

namespace OAI

/-! # Removing the finite positive-denominator singular-series cutoff -/

namespace JointDickman
open Finset
open scoped ArithmeticFunction.Moebius

theorem sum_positiveDenominators {E : Type*} [AddCommMonoid E] (Q : ℕ)
    (f : ℕ → E) (hf : f 0 = 0) :
    (∑ q ∈ positiveDenominators Q, f (q : ℕ)) = ∑ q ∈ range (Q+1), f q := by
  classical
  calc
    _ = ∑ q ∈ (range (Q+1)).filter (fun n => 0 < n), f q :=
      sum_subtype_eq_sum_filter f
    _ = _ := by
      apply sum_subset (filter_subset _ _)
      intro n hn hnnot
      have hn0 : n = 0 := by
        have hnp : ¬ 0 < n := fun hpos => hnnot (mem_filter.mpr ⟨hn,hpos⟩)
        omega
      simpa only [hn0] using hf

theorem singularSeries_positive_truncation_error
    (hMP : PublishedInputs.PrimeProductMertensInput) (j Q : ℕ) :
    |((j : ℝ)/j.totient)*(∑ q ∈ positiveDenominators Q, singularSeriesCoefficient j (q : ℕ))-
      singularSeries j| ≤ ((j : ℝ)/j.totient)*singularSeriesTail (Q+1) := by
  rw [sum_positiveDenominators Q _ (by simp [singularSeriesCoefficient])]
  unfold singularSeries
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (j : ℝ)/j.totient)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := singularSeries_tail_bound hMP j (Q+1)
  simpa only [Real.norm_eq_abs,abs_sub_comm] using h

theorem projected_major_integral_error (hMP : PublishedInputs.PrimeProductMertensInput)
    (j Q : ℕ) [NeZero j] (L U : ℝ) (W A B : ℝ → ℂ) :
    ‖(∑ q ∈ positiveDenominators Q, ((μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))*
      (∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then
        ∫ ξ in L..U, W ξ*
          ((ramanujanSum (j*(q : ℕ)) h/((j*(q : ℕ)).totient : ℂ))*A ξ)*
          ((ramanujanSum (j*(q : ℕ)) (-h)/((j*(q : ℕ)).totient : ℂ))*B ξ)
      else 0))-(singularSeries j : ℂ)*(∫ ξ in L..U, W ξ*A ξ*B ξ)‖ ≤
      ((j : ℝ)/j.totient)*singularSeriesTail (Q+1)*‖∫ ξ in L..U, W ξ*A ξ*B ξ‖ := by
  rw [projected_major_integral,← sub_mul,norm_mul,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (singularSeries_positive_truncation_error hMP j Q)
    (norm_nonneg _)

end JointDickman

end OAI
