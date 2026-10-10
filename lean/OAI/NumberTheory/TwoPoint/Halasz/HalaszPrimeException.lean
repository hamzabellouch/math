import OAI.NumberTheory.TwoPoint.Halasz.HalaszExceptionalWindow

namespace OAI

/-! The prime mean-square bound with one exceptional frequency window. -/
namespace TwoPointCorrelations

open Finset MeasureTheory

theorem halasz_prime_window_exception : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (x δ T A W c : ℝ), 0 < x → 0 < δ → δ ≤ 1 → B ≤ T → 0 ≤ A → 0 ≤ W →
    ∀ (P Q : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T^2 ≤ (p:ℝ)) →
      (∀ q ∈ Q, q.Prime) → ∀ (a b : ℕ → ℂ) (F : ℝ → ℂ),
      let P₁ := mrtExponentialPolynomial P
        (fun p => a p*((Real.log (p:ℝ)/p:ℝ):ℂ)) (fun p => -Real.log (p:ℝ))
      let Q₁ := mrtExponentialPolynomial Q
        (fun q => b q*((Real.log (q:ℝ)/q:ℝ):ℂ)) (fun q => -Real.log (q:ℝ))
      IntegrableOn (fun t => P₁ t*Q₁ t*F t*
        halaszPerronWindowKernel x δ (1+(t:ℂ)*Complex.I)) (Set.Ioc (-T) T) →
      (∀ t ∈ Set.Ioc (-T) T, t ∉ Set.Ioc (c-1/2) (c+1/2) → ‖F t‖ ≤ A) →
      (∀ t ∈ Set.Ioc (-T) T, ‖F t‖ ≤ W) →
      ‖∫ t in -T..T, P₁ t*Q₁ t*F t*
        halaszPerronWindowKernel x δ (1+(t:ℂ)*Complex.I)‖ ≤
      (C*x*(A+W/(1+|c|)))*
        (Real.sqrt (∑ p ∈ P, ‖a p‖^2*(Real.log (p:ℝ)/p))*
          Real.sqrt (∑ q ∈ Q, ‖b q‖^2*(Real.log (q:ℝ)/q))) := by
  obtain ⟨C₁,B,hC₁,hB,hfirst⟩ := halasz_prime_mean_square
  obtain ⟨C₂,hC₂,hsecond⟩ := halasz_prime_mean_square_cauchy
  obtain ⟨C₃,hC₃,hunit⟩ := halasz_prime_mean_square_unit
  let C := 4*Real.sqrt C₁*Real.sqrt C₂+12*C₃
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,B,hC,hB,?_⟩
  intro x δ T A W c hx hδ hδ1 hBT hA hW P Q hP hQ a b F
  dsimp only
  intro hi hFA hFW
  let P₁ := mrtExponentialPolynomial P
    (fun p => a p*((Real.log (p:ℝ)/p:ℝ):ℂ)) (fun p => -Real.log (p:ℝ))
  let Q₁ := mrtExponentialPolynomial Q
    (fun q => b q*((Real.log (q:ℝ)/q:ℝ):ℂ)) (fun q => -Real.log (q:ℝ))
  let Mp := ∑ p ∈ P, ‖a p‖^2*(Real.log (p:ℝ)/p)
  let Mq := ∑ q ∈ Q, ‖b q‖^2*(Real.log (q:ℝ)/q)
  have hT : 0 ≤ T := (show (0:ℝ) ≤ B by linarith).trans hBT
  have hp : (∫ t in -T..T, ‖P₁ t‖^2) ≤ C₁*Mp := hfirst T P hBT hP a
  have hqi := halasz_cauchy_polynomial_integrable Q
    (fun q => b q*((Real.log (q:ℝ)/q:ℝ):ℂ)) (fun q => -Real.log (q:ℝ))
  have hq : (∫ t in -T..T, ‖Q₁ t‖^2*(1+t^2)⁻¹) ≤ C₂*Mq := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
    exact (setIntegral_le_integral hqi (Filter.Eventually.of_forall (fun t => by positivity))).trans
      (hsecond Q hQ b)
  have hpu : (∫ t in (c-1/2)..(c+1/2), ‖P₁ t‖^2) ≤ C₃*Mp :=
    hunit P (fun p hp => (hP p hp).1) a c
  have hqu : (∫ t in (c-1/2)..(c+1/2), ‖Q₁ t‖^2) ≤ C₃*Mq := hunit Q hQ b c
  have hmid := halasz_window_middle_exception hx hδ hδ1 hT hA hW P₁ Q₁ F
    (halasz_polynomial_continuous P _ _) (halasz_polynomial_continuous Q _ _) hi hFA hFW
  apply hmid.trans
  calc
    _ ≤ (4*x*A)*(Real.sqrt (C₁*Mp)*Real.sqrt (C₂*Mq)) +
        (12*x*W/(1+|c|))*(Real.sqrt (C₃*Mp)*Real.sqrt (C₃*Mq)) := by
      gcongr
    _ = (4*Real.sqrt C₁*Real.sqrt C₂*x*A+12*C₃*x*(W/(1+|c|)))*
        (Real.sqrt Mp*Real.sqrt Mq) := by
      simp only [Real.sqrt_mul hC₁.le,Real.sqrt_mul hC₂.le,Real.sqrt_mul hC₃.le]
      conv_rhs => rw [← Real.sq_sqrt hC₃.le]
      ring
    _ ≤ (C*x*(A+W/(1+|c|)))*(Real.sqrt Mp*Real.sqrt Mq) := by
      have hmain : 4*Real.sqrt C₁*Real.sqrt C₂ ≤ C :=
        le_add_of_nonneg_right (by positivity)
      have hbad : 12*C₃ ≤ C := le_add_of_nonneg_left (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hmain (show 0 ≤ x*A by positivity),
        mul_le_mul_of_nonneg_right hbad (show 0 ≤ x*(W/(1+|c|)) by positivity)]

end TwoPointCorrelations

end OAI
