import OAI.NumberTheory.CubicMoment.Estimates.SinglePrimeSupport
import OAI.NumberTheory.CubicMoment.Estimates.CenteredPrimeBilinear

namespace OAI

/-! The published-input bilinear theorem specialized to one actual prime
coordinate. No tuple multiplicity or squarefree filter remains hidden in
the conclusion used by the semiprime pieces. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem single_prime_centered_bilinear {γ : Type*}
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W)
    (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (k d U : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K T₀ : ℝ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u : ℝ) (P : Finset Eisenstein) (α : Eisenstein → ℂ),
      T₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/16) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      |u| ≤ (1+Real.log (L r))^U →
      (∀ a ∈ P, primary a ∧ norm a/A ∈ Set.Icc 1 2) →
      (∑ a ∈ P, ‖α a‖^2) ≤ M*A*(1+Real.log (L r))^d →
      ‖∑ a ∈ P, ∑ p ∈ fullPrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) (),
          α a*W r (norm p/L r)*centeredGauss (a*p)*normTwist u (a*p)‖ ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^k := by
  have hWF : LogarithmicWeightFamily (fun z : γ × Unit => L z.1)
      (fun z => W z.1) := by
    refine ⟨fun z => hL z.1,fun z => hW.compact z.1,fun z => hW.positive z.1,
      fun z => hW.smooth z.1,hW.radius,hW.radius_nonneg,
      fun z => hW.support_bound z.1,?_⟩
    intro n
    obtain ⟨B,hB,hb⟩ := hW.derivative_bound n
    exact ⟨B,0,hB,by simpa only [pow_zero,mul_one] using fun z : γ × Unit => hb z.1⟩
  obtain ⟨η,σ,G,K,T₀,hη,hη1,hσ,hK,hbound⟩ := rough_prime_centered_bilinear
    (ι := Unit) (c := 1/2) (R := 2) (Q := 2) (M := M)
    hSW hpub hHuxley hperiod hMV hC (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hM hGI hGQ hVor hGamma L (fun r _ => W r) hL hWF
    (fun r _ => hlo r) (fun r _ => hhi r) k d U
  refine ⟨η,G,K,T₀,hη,hη1,hK,?_⟩
  intro r A u P α hT hrough hAlo hAhi hu hP hα
  have hb := hbound r (fun _ => L r) A 1 u P α hT (by simp) (fun _ => hrough)
    hAlo hAhi one_ne_zero (by simpa [norm] using Real.one_le_rpow (hL r) hσ.le) hu hP hα
  rw [fullSquarefreePrimeSupport_unit] at hb
  convert hb using 1
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro p hp
  rw [fullPrimeCoefficient_unit hp]

end CubicFirstMoment

end

end OAI
