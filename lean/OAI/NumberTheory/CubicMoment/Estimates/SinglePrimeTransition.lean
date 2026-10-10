import OAI.NumberTheory.CubicMoment.Estimates.SinglePrimeVariance

namespace OAI

/-! The cube bound at the transition keeps the coefficient l¹ mass,
and the full prime variance keeps its diagonal l² mass. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem prime_variance_transition_bound (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hVM : ∀ x, ‖V x‖ ≤ M) (hcut : ∀ x, R < x → V x = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein),
      (∀ p ∈ S, primaryPrime p) → ∀ (β : Eisenstein → ℂ) (u A B : ℝ),
      0 < A → 0 < B → A ≤ B^2 → (∀ p ∈ S, B ≤ norm p) →
      (∀ p ∈ S, ∀ q ∈ S,
        (∑ r ∈ primaryPrimeFactors p ∪ primaryPrimeFactors q, 1/norm r) ≤ 4) →
      ‖smoothedDispersionVariance S β u V A‖ ≤
        K*A*(∑ p ∈ S, ‖β p‖^2) +
        K*A^(2/3:ℝ)*B^(-(1/3:ℝ))*(∑ p ∈ S, ‖β p‖)^2 +
        ‖noncubePoissonContribution S β u V A‖ := by
  obtain ⟨C,D,hC,hD,hcube⟩ := cubePoissonContribution_uniform_error V hV hV'
  let K₀ := C+4*D+‖cubeProfileIntegral V‖
  let K := K₀+18*R*M+1
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
  have hK : 0 < K := by dsimp [K,K₀]; positivity
  refine ⟨K,hK,?_⟩
  intro S hS β u A B hA hB hAB hN hrough
  let t := A^(2/3:ℝ)*B^(-(1/3:ℝ))
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hdiag := prime_dispersion_diagonal_bound S hS β u V hA hR hM hVM hcut
  have hc := hcube S (fun p hp => ⟨(hS p hp).1,(hS p hp).2.squarefree⟩)
    A B 4 hA hB (by norm_num) (hAB.trans (by nlinarith [sq_nonneg B])) hN hrough β u
  have hm := coprimeCubeMainTerm_norm_bound S β u V hA.le hB hN
  have hscale := cube_transition_scale hA hB hAB
  have hfirst : C*A/(27*B) ≤ C*t := by
    calc
      _ = C*(A/B)/27 := by ring
      _ ≤ C*(A/B) := div_le_self (by positivity) (by norm_num)
      _ ≤ C*t := mul_le_mul_of_nonneg_left hscale hC.le
  have hcoef : C*A/(27*B)+D*t*4/9+t/9*‖cubeProfileIntegral V‖ ≤ K₀*t := by
    dsimp [K₀]
    nlinarith [mul_nonneg hD.le ht,mul_nonneg ht (_root_.norm_nonneg (cubeProfileIntegral V))]
  have hcubebound : ‖cubePoissonContribution S β u V A‖ ≤
      K₀*t*(∑ p ∈ S, ‖β p‖)^2 := by
    apply (norm_le_norm_sub_add (cubePoissonContribution S β u V A)
      (coprimeCubeMainTerm S β u V A)).trans
    apply ((add_le_add hc hm).trans_eq ?_).trans
      (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
    dsimp [t]
    ring
  have hKS : K₀ ≤ K := by
    have hh : 0 ≤ 18*R*M := by positivity
    dsimp [K]
    linarith
  have hKD : 18*R*M ≤ K := by dsimp [K]; linarith
  have hmain (p : Eisenstein) (hp : p ∈ S) : primary p ∧ Squarefree p ∧ p ≠ 1 :=
    ⟨(hS p hp).1,(hS p hp).2.squarefree,fun h => (hS p hp).2.not_isUnit (h ▸ isUnit_one)⟩
  rw [prime_variance_split S hS β u V hV hV' hA,
    coprimeDispersionGram_split S hmain β u V hV hV' hA]
  apply (norm_add_le _ _).trans
  apply (add_le_add hdiag ((norm_add_le _ _).trans
    (add_le_add hcubebound (le_refl _)))).trans
  dsimp [t]
  have he : 0 ≤ ∑ p ∈ S, ‖β p‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hd := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKD hA.le) he
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKS ht) (sq_nonneg (∑ p ∈ S, ‖β p‖))
  dsimp [t] at hb
  nlinarith

end CubicFirstMoment

end

end OAI
