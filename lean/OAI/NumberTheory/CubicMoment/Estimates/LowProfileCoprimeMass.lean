import OAI.NumberTheory.CubicMoment.Estimates.PoissonProfileBudget
import OAI.NumberTheory.CubicMoment.Estimates.DivisorLowAllFrequency

namespace OAI

/-! Low-height coprimality mass with its profile cost retained explicitly. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment.ProfileControl

theorem low_coprime_mellin_height_log_saving (hpnt : PrimaryPrimePNT) (k : ℕ)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (q : ℕ) (hq : q ≤ 3) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (P : PoissonProfileBudget) (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T M u ρ N : ℝ), 65536 ≤ (Z:ℝ) → 1 ≤ B → 0 ≤ M →
      (1+Real.log Z)^Ct ≤ T → 0 ≤ ρ → 0 < N →
      (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      8*B ≤ (Z:ℝ)^(3/4:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖normDenominatorMellinCoefficient poissonProfileLogWidth poissonProfileLogWidth_pos P.V P.compact P.smooth ρ s‖*
          twistedCoprimeMellinMass S H U β (fun a => norm a/N) (t+u) s) T ≤
        (K*P.cost)*M^2*(Z:ℝ)^2*B^(1/3:ℝ)/(1+Real.log Z)^k := by
  obtain ⟨K,Ct,hK,hpower⟩ := divisor_all_frequency_low_log_saving hpnt hMV hC hHuxley k
  refine ⟨K,Ct,hK,?_⟩
  intro P S H U β Z B T M u ρ N hZ hB hM hT hρ hN hU hS hβ hsize hH
  let G := divisorCharacterMass S H U β
  let A := K*M^2*(Z:ℝ)^2*B^(1/3:ℝ)/(1+Real.log Z)^k
  let E := ∑ d ∈ U.powerset, (H.card:ℝ)*(S.filter (fun a => (∏ p ∈ d, p) ∣ a)).card*
    ∑ a ∈ S.filter (fun a => (∏ p ∈ d, p) ∣ a), ‖β a‖^2
  have hZ1 : 1 ≤ (Z:ℝ) := by linarith
  have hlog : 0 < 1+Real.log (Z:ℝ) := by linarith [Real.log_nonneg hZ1]
  have hTp : 0 < T := (pow_pos hlog _).trans_le hT
  have hh := normMellin_signed_height_of_mass poissonProfileLogWidth poissonProfileLogWidth_pos
    P.V P.compact P.smooth q P.cost (fun x hx => P.mellin_le hq x hx) ρ hρ G (divisorCharacterMass_continuous S H U β) E A T u
    (by dsimp [A]; positivity) hTp
    (fun t => divisorCharacterMass_bound S H U β (fun a ha => (hS a ha).1) t)
    (fun v => hpower S H U β Z B T M v hZ hB hM hT hU hS hβ hsize hH)
  have he (t s : ℝ) := twistedCoprimeMellinMass_eq_divisor_mass S H U β
    (fun a ha => (hS a ha).1) (t+u) s hN
  simp_rw [he]
  convert hh using 1
  dsimp [A]
  ring

end CubicFirstMoment.ProfileControl

end

end OAI
