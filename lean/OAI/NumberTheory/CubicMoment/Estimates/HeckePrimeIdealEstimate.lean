import OAI.NumberTheory.CubicMoment.Estimates.HeckeFullPrimeEstimate
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerAbsorption

namespace OAI

/-! Uniform sharp prime-ideal cancellation from the actual Hecke pair
functional equations. Higher prime powers have been removed by a proved count. -/
noncomputable section
namespace CubicFirstMoment

theorem hecke_prime_ideal_bound_of_analytic_pair :
    ∃ B c X0 : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1/4 ∧ 1 < X0 ∧
    ∀ {χ χdual χ2dual : EisensteinIdealExponent → ℂ}, (∀ ν, ‖χ ν‖ ≤ 1) →
    χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
    (∀ ν, ‖χdual ν‖ ≤ 1) → (∀ ν, ‖χ2dual ν‖ ≤ 1) →
    ∀ {L Ldual L2 L2dual : ℂ → ℂ}, Differentiable ℂ L → Differentiable ℂ L2 →
    (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s) →
    (∀ s : ℂ, 1 < s.re → L2dual s=normDirichletSeries χ2dual idealExponentNorm s) →
    ∀ {A A2 k k2 Q : ℝ} {ε ε2 : ℂ},
    0 < A → 0 < A2 → 0 ≤ k → 0 ≤ k2 → ‖ε‖ ≤ 1 → ‖ε2‖ ≤ 1 →
    1 ≤ Q → A ≤ Q → A2 ≤ Q → k+7 ≤ Q → k2+7 ≤ Q →
    HeckeFunctionalEquation A k ε L Ldual →
    HeckeFunctionalEquation A2 k2 ε2 L2 L2dual →
    ShiftedCompletedHeckeFiniteOrder A k L → ShiftedCompletedHeckeFiniteOrder A2 k2 L2 →
    ∀ X : ℝ, X0 ≤ X →
      ‖idealPrimeChebyshev χ X‖ ≤
        B*(X*(Real.log (X*Q))^2*Real.exp (-c*Real.log X/primeContourDenominator Q X)) := by
  obtain ⟨B,c,Y0,hB,hc,hc1,hY0,hbound⟩ := hecke_full_prime_bound_of_analytic_pair
  let X0 := max Y0 (Real.exp 2)
  have hX0 : 1 < X0 := hY0.trans_le (le_max_left _ _)
  refine ⟨B+idealPrimePowerErrorConstant,c,X0,add_pos hB idealPrimePowerErrorConstant_pos,
    hc,hc1,hX0,?_⟩
  intro χ χdual χ2dual hχ hχ0 hχadd hχdual hχ2dual L Ldual L2 L2dual hL hL2
    hs hs2 hds hds2 A A2 k k2 Q ε ε2 hA hA2 hk hk2 hε hε2 hQ hQA hQA2 hQk hQk2
    hFE hFE2 hcomp hcomp2 X hX
  have hXp : 0 < X := zero_lt_one.trans (hX0.trans_le hX)
  have hLX : 2 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 2) ((le_max_right _ _).trans hX)
    rwa [Real.log_exp] at hh
  have hmain := hbound hχ hχ0 hχadd hχdual hχ2dual hL hL2 hs hs2 hds hds2 hA hA2 hk hk2 hε hε2
    hQ hQA hQA2 hQk hQk2 hFE hFE2 hcomp hcomp2 X ((le_max_left _ _).trans hX)
  exact idealPrimeChebyshev_bound_of_mangoldt χ hχ hc.le hc1 hQ hXp hLX hmain

end CubicFirstMoment

end

end OAI
