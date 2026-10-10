import OAI.NumberTheory.CubicMoment.Estimates.SinglePrimeSupport
import OAI.NumberTheory.CubicMoment.Estimates.HeightBilinearScale
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeSmoothWeights

namespace OAI

/-! The published-input height mean for a single genuine prime coordinate.
This is used for the complementary Mellin frequencies of the semiprime branch. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def uniformLogWeights_prime_coordinates {γ : Type*} (L : γ → ℝ)
    (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r) (hW : UniformLogWeights W) :
    LogarithmicWeightFamily (fun z : γ × Unit => L z.1) (fun z => W z.1) := by
  refine ⟨fun z => hL z.1,fun z => hW.compact z.1,fun z => hW.positive z.1,
    fun z => hW.smooth z.1,hW.radius,hW.radius_nonneg,
    fun z => hW.support_bound z.1,?_⟩
  intro n
  obtain ⟨B,hB,hb⟩ := hW.derivative_bound n
  exact ⟨B,0,hB,by simpa only [pow_zero,mul_one] using fun z : γ × Unit => hb z.1⟩

theorem single_prime_height_bilinear {γ : Type*}
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W)
    (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (k d : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u T : ℝ) (P : Finset Eisenstein) (α : Eisenstein → ℂ),
      B₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      (1+Real.log (L r))^m ≤ T → T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
      (∀ a ∈ P, primary a ∧ norm a/A ∈ Set.Icc 1 2) →
      (∑ a ∈ P, ‖α a‖^2) ≤ M*A*(1+Real.log (L r))^d →
      dyadicHeightMean (fun t =>
        ‖∑ a ∈ P, ∑ p ∈ fullPrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) (),
          α a*W r (norm p/L r)*gauss (a*p)*normTwist (u+t) (a*p)‖) T ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη1,hσ,hbound⟩ := rough_prime_height_bilinear
    (γ := γ) (ι := Unit) (c := 1/2) (R := 2) (Q := 2) (M := M)
    hpub hHuxley hperiod hMV hC (by norm_num) (by norm_num) (by norm_num)
    hM hGI hGQ k d
  obtain ⟨G,K,B₀,m,hK,hbound⟩ := hbound L (fun r _ => W r) hL
    (uniformLogWeights_prime_coordinates L W hL hW)
    (fun r _ => hlo r) (fun r _ => hhi r)
  refine ⟨η,G,K,B₀,m,hη,hη1,hK,?_⟩
  intro r A u T P α hB hrough hAlo hAhi hT hThi hu hP hα
  have hb := hbound r (fun _ => L r) A 1 u T P α hB (by simp) (fun _ => hrough)
    hAlo hAhi one_ne_zero (by simpa [norm] using Real.one_le_rpow (hL r) hσ.le)
    hT hThi hu hP hα
  rw [fullSquarefreePrimeSupport_unit] at hb
  convert hb using 1
  congr 1
  funext t
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro p hp
  rw [fullPrimeCoefficient_unit hp]

end CubicFirstMoment

end

end OAI
