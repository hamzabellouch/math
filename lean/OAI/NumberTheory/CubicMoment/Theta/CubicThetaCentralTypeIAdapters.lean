import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAllTypeILow
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTypeIMixedLow

namespace OAI

/-! The existing low-height interfaces follow from the proved actual theta
transform, including its normalized radial constant. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem typeI_low_actual
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) (_hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {B A : ℝ} (hB : 1 ≤ B) (hA : 0 ≤ A) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      ‖∑ r ∈ S, α r*(metaplecticAngularSmoothSum r ℓ (W (w r)) U 0-
        angularSmoothModel r ℓ (W (w r)) U)‖ ≤ K*X^(5/6-1/100:ℝ) :=
  cubicTheta_typeI_low hW ℓ hB hA k

theorem typeI_mixed_low_actual
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (_hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {B D : ℝ} (hB : 1 ≤ B) (hD : 0 ≤ D) (k d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (β : Eisenstein → ℂ) (X R U : ℝ),
      2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖β r‖ ≤ D*((metaplecticPrimaryDivisors r).card:ℝ)^k*(1+Real.log X)^d) →
      ‖∑ r ∈ S, β r*(typeIMixedGauss r (W (w r)) U-typeIMixedModel r (W (w r)) U)‖ ≤
        K*U^(-1/6:ℝ)*X^(5/6-1/100:ℝ) :=
  cubicTheta_typeI_mixed_low hW hB hD k d

end CubicFirstMoment

end

end OAI
