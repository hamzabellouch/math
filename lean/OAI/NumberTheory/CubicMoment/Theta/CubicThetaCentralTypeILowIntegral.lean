import OAI.NumberTheory.CubicMoment.Estimates.TypeILowIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralTypeILowHeightTwist

namespace OAI

/-! Integrating the proved low Type-I estimate against the actual central
height weight. Outer-level and interval phases have modulus one. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment


theorem typeI_low_integral_bound_actual
    {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ} (hW : LogarithmicWeightFamily Y W)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {B A : ℝ} (hB : 1 ≤ B) (hA : 0 ≤ A) (k Ct : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : Eisenstein → γ) (S : Finset Eisenstein)
      (α : Eisenstein → ℂ) (X R U H X₀ : ℝ),
      2 ≤ X → 1 ≤ Real.log X → B ≤ X → 1 ≤ R → 1 ≤ U → R*U = X →
      R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, Y (w r) = X) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → W (w r) x = 0) →
      (∀ r ∈ S, ‖α r‖ ≤ A*((metaplecticPrimaryDivisors r).card:ℝ)^k) →
      ‖lowTypeIIntegral w S α W ℓ U H ((1+Real.log X)^Ct) X₀‖ ≤
        K*(1+Real.log X)^Ct*X^(5/6-1/100:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := typeI_low_height_twist_actual  hW ℓ hGamma hB hA k (Ct+1)
  refine ⟨(8/3)*Real.log 2*K,by positivity,?_⟩
  intro w S α X R U H X₀ hX hlog hBX hR hU hRU hRhi hS hY hcut hα
  have hL : 0 < 1+Real.log X := by linarith
  have hT : 0 < (1+Real.log X)^Ct := pow_pos hL _
  have hf (t : ℝ) (ht : t ∈ Set.Icc (-(4/3)*((1+Real.log X)^Ct))
      ((4/3)*((1+Real.log X)^Ct))) :
      ‖Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*
        ∑ r ∈ S, (α r*normTwist t r)*lowTwistedTypeIRow r ℓ (W (w r)) U t‖ ≤
        K*X^(5/6-1/100:ℝ) := by
    rw [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
    apply hbound w S (fun r => α r*normTwist t r) X R U t
      hX hBX hR hU hRU hRhi hS hY hcut
    · intro r hr
      simpa only [norm_mul,norm_normTwist,mul_one] using hα r hr
    · have habs : |t| ≤ (4/3)*((1+Real.log X)^Ct) := by
        apply abs_le.mpr
        exact ⟨by linarith [ht.1],ht.2⟩
      apply habs.trans
      rw [pow_succ]
      nlinarith [pow_nonneg hL.le Ct]
  have hb := lowHeightWeight_integral_bound H hT (show 0 ≤ K*X^(5/6-1/100:ℝ) by positivity)
    _ hf
  change ‖lowTypeIIntegral w S α W ℓ U H ((1+Real.log X)^Ct) X₀‖ ≤ _ at hb
  apply hb.trans_eq
  ring

end CubicFirstMoment

end

end OAI
