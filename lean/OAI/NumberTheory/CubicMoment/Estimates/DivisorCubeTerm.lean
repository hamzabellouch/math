import OAI.NumberTheory.CubicMoment.Estimates.DivisorCubeSeries
import OAI.NumberTheory.CubicMoment.Estimates.CubeUniformError

namespace OAI

/-! The actual principal part of a square-divisor Poisson block, with
the square-divisor density kept explicitly. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def divisorCubePoissonContribution (d : Eisenstein) (S : Finset Eisenstein)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      ((A/(norm d)^2)/(9*Real.sqrt (norm (b*a))):ℝ)*
      ∑' h : Eisenstein, if h ≠ 0 ∧ (∃ j : Eisenstein, j^3 = d*h) then
        mixedSymbol b a (d^2)*gramDualTerm b a W (A/(norm d)^2) h else 0
    else 0

theorem divisorCubePoissonContribution_eq {d : Eisenstein} (hd : primary d)
    (hs : Squarefree d) (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ IsCoprime a d)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) :
    divisorCubePoissonContribution d S β u W A =
      (1/(norm d)^2:ℝ)*cubePoissonContribution S β u W A := by
  unfold divisorCubePoissonContribution cubePoissonContribution
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    rw [divisor_cube_series_effective (hS a ha).1 (hS b hb).1 hd hs
      (hS a ha).2 (hS b hb).2 W hA]
    simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_one]
    ring
  · simp only [ite_eq_right hab,mul_zero]

theorem divisorCubePoissonContribution_uniform_error (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (d : Eisenstein), primary d → Squarefree d →
      ∀ (S : Finset Eisenstein), (∀ a ∈ S, primary a ∧ Squarefree a ∧ IsCoprime a d) →
      ∀ (A L P : ℝ), 0 < A → 0 < L → 0 ≤ P → A ≤ 27*L^2 →
      (∀ a ∈ S, L ≤ norm a) →
      (∀ a ∈ S, ∀ b ∈ S, (∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p) ≤ P) →
      ∀ (β : Eisenstein → ℂ) (u : ℝ),
      ‖divisorCubePoissonContribution d S β u W A -
          (1/(norm d)^2:ℝ)*coprimeCubeMainTerm S β u W A‖ ≤
        ((C*A/(27*L)+K*A^(2/3:ℝ)*L^(-(1/3:ℝ))*P/9)*
          (∑ a ∈ S, ‖β a‖)^2)/(norm d)^2 := by
  obtain ⟨C,K,hC,hK,hbound⟩ := cubePoissonContribution_uniform_error W hW hW'
  refine ⟨C,K,hC,hK,?_⟩
  intro d hd hs S hS A L P hA hL hP hAL hN hp β u
  rw [divisorCubePoissonContribution_eq hd hs S (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩)
    β u W hA.le,← mul_sub,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (show 0 ≤ 1/(norm d)^2 by positivity)]
  have hb := hbound S (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩)
    A L P hA hL hP hAL hN hp β u
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
