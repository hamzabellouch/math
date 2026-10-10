import OAI.NumberTheory.CubicMoment.Estimates.CubeFiniteError

namespace OAI

/-! Uniform cube error on a norm annulus. The first term is the lattice
error; the second records the actual reciprocal-prime exclusion loss. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cube_pair_norm_bounds {L : ℝ} (hL : 0 < L) {a b : Eisenstein}
    (ha : L ≤ norm a) (hb : L ≤ norm b) :
    L ≤ Real.sqrt (norm (b*a)) ∧ (norm (b*a))^(-(1/6:ℝ)) ≤ L^(-(1/3:ℝ)) := by
  have hN : L^2 ≤ norm (b*a) := by
    rw [norm_mul_eq,pow_two]
    exact mul_le_mul hb ha hL.le (hL.le.trans hb)
  constructor
  · have h := Real.sqrt_le_sqrt hN
    simpa only [Real.sqrt_sq hL.le] using h
  · apply (Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hL) hN (by norm_num)).trans_eq
    rw [← Real.rpow_natCast L 2,← Real.rpow_mul hL.le]
    norm_num

theorem cubePoissonContribution_uniform_error (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (S : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      ∀ (A L P : ℝ), 0 < A → 0 < L → 0 ≤ P → A ≤ 27*L^2 →
      (∀ a ∈ S, L ≤ norm a) →
      (∀ a ∈ S, ∀ b ∈ S,
        (∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p) ≤ P) →
      ∀ (β : Eisenstein → ℂ) (u : ℝ),
      ‖cubePoissonContribution S β u W A-coprimeCubeMainTerm S β u W A‖ ≤
        (C*A/(27*L)+K*A^(2/3:ℝ)*L^(-(1/3:ℝ))*P/9)*(∑ a ∈ S, ‖β a‖)^2 := by
  obtain ⟨C,K,hC,hK,hbound⟩ := cubePoissonContribution_error W hW hW'
  refine ⟨C,K,hC,hK,?_⟩
  intro S hS A L P hA hL hP hAL hN hprime β u
  have hAN (a : Eisenstein) (ha : a ∈ S) (b : Eisenstein) (hb : b ∈ S) :
      A ≤ 27*norm (b*a) := by
    apply hAL.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [norm_mul_eq,pow_two]
    exact mul_le_mul (hN b hb) (hN a ha) hL.le (hL.le.trans (hN b hb))
  let M := C*A/(27*L)+K*A^(2/3:ℝ)*L^(-(1/3:ℝ))*P/9
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hrow (a : Eisenstein) (ha : a ∈ S) (b : Eisenstein) (hb : b ∈ S) :
      C*A/(27*Real.sqrt (norm (b*a))) +
        K*(A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9)*
          ∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p ≤ M := by
    obtain ⟨hs,hr⟩ := cube_pair_norm_bounds hL (hN a ha) (hN b hb)
    apply add_le_add
    · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    · calc
        _ ≤ K*(A^(2/3:ℝ)*L^(-(1/3:ℝ))/9)*P := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by positivity)) (by norm_num)) hK.le
          · exact hprime a ha b hb
          · exact Finset.sum_nonneg (fun p _ => one_div_nonneg.mpr (norm_nonneg p))
          · positivity
        _ = _ := by ring
  apply (hbound S hS A hA hAN β u).trans
  calc
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, ‖β a‖*‖β b‖*M := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      split_ifs
      · exact mul_le_mul_of_nonneg_left (hrow a ha b hb) (by positivity)
      · positivity
    _ = _ := by
      dsimp only [M]
      simp only [pow_two,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring

end CubicFirstMoment

end

end OAI
