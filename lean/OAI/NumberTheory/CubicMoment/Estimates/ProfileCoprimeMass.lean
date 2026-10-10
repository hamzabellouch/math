import OAI.NumberTheory.CubicMoment.Estimates.PoissonProfileBudget
import OAI.NumberTheory.CubicMoment.Estimates.SmallBCoprimeMass

namespace OAI

/-! Small-B coprimality mass with its profile cost retained explicitly. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment.ProfileControl

theorem smallB_coprime_mellin_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (q : ℕ) (hq : q ≤ 3) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : PoissonProfileBudget) (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T u ρ N : ℝ), 1 ≤ (Z:ℝ) → 1 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T → 0 ≤ ρ → 0 < N →
      (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(3/4:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖normDenominatorMellinCoefficient poissonProfileLogWidth poissonProfileLogWidth_pos P.V P.compact P.smooth ρ s‖*
          twistedCoprimeMellinMass S H U β (fun a => norm a/N) (t+u) s) T ≤
        (K*P.cost)*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hpower⟩ := smallB_divisor_height_power hMV hC hHuxley
  refine ⟨K,hK,?_⟩
  intro P S H U β Z B T u ρ N hZ hB hT hρ hN hU hS hsize hH
  let G := divisorCharacterMass S H U β
  let A := K*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ a ∈ S, ‖β a‖^2
  let E := ∑ d ∈ U.powerset, (H.card:ℝ)*(S.filter (fun a => (∏ p ∈ d, p) ∣ a)).card*
    ∑ a ∈ S.filter (fun a => (∏ p ∈ d, p) ∣ a), ‖β a‖^2
  have hTp : 0 < T := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _).trans_le hT
  have hh := normMellin_signed_height_of_mass poissonProfileLogWidth poissonProfileLogWidth_pos
    P.V P.compact P.smooth q P.cost (fun x hx => P.mellin_le hq x hx) ρ hρ G (divisorCharacterMass_continuous S H U β) E A T u
    (by dsimp [A]; positivity) hTp
    (fun t => divisorCharacterMass_bound S H U β (fun a ha => (hS a ha).1) t)
    (fun v => hpower S H U β Z B T v hZ hB hT hU hS hsize hH)
  have he (t s : ℝ) := twistedCoprimeMellinMass_eq_divisor_mass S H U β
    (fun a ha => (hS a ha).1) (t+u) s hN
  simp_rw [he]
  convert hh using 1
  dsimp [A]
  ring

end CubicFirstMoment.ProfileControl

end

end OAI
