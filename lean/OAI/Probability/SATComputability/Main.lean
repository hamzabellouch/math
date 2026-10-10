import OAI.Probability.SATComputability.SupercriticalEnergy
import OAI.Probability.SATComputability.PressureUpper
import OAI.Probability.SATComputability.TrialCompleteness
import OAI.Probability.SATComputability.LowerProgram

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter
open scoped Topology NNReal

theorem satTrialSeparation : TrialSeparation satTrialEvaluation (limitingCenter 3) := by
  constructor
  · exact fun _ hj hn => satTrialEvaluation_sound hj hn
  · intro a ha
    have haR : (0 : ℝ) < a := (limitingCenter_pos 3 (by decide)).trans ha
    have haQ : 0 < a := by exact_mod_cast haR
    let aNN : ℝ≥0 := ⟨a,haR.le⟩
    have haNN : 0 < aNN := haR
    obtain ⟨ε,hε,hV⟩ := relaxedPoissonMinimum_supercritical (a := aNN) ha
    obtain ⟨b,hb,hnegative⟩ := negative_pressure_of_violation_density haNN hε hV
    exact satTrialEvaluation_negative_witness a haQ b hb hnegative

theorem threshold_program :
    ∃ (q : ℕ → ℚ) (c : Nat.Partrec.Code),
      Computable q ∧
      (∀ r, c.eval r = Part.some (Encodable.encode (q r))) ∧
      (∀ r, |(q r : ℝ)-limitingCenter 3| ≤ (2^r : ℝ)⁻¹) :=
  threshold_program_of_trial_separation satTrialSeparation

def MainStatement : Prop :=
    ∃ (α : ℝ) (q : ℕ → ℚ) (c : Nat.Partrec.Code),
      0 < α ∧
      (∀ a : ℝ, 0 ≤ a → a < α →
        Tendsto (fun n : ℕ => properSATProbability n 3 ⌊a*(n : ℝ)⌋₊) atTop (nhds 1)) ∧
      (∀ a : ℝ, α < a →
        Tendsto (fun n : ℕ => properSATProbability n 3 ⌊a*(n : ℝ)⌋₊) atTop (nhds 0)) ∧
      Computable (fun r => Encodable.encode (q r)) ∧
      (∀ r, c.eval r = Part.some (Encodable.encode (q r))) ∧
      (∀ r, |(q r : ℝ)-α| ≤ (2^r : ℝ)⁻¹)

theorem main : MainStatement := by
  obtain ⟨q,c,hq,hc,he⟩ := threshold_program
  exact ⟨limitingCenter 3,q,c,limitingCenter_pos 3 (by decide),
    subcritical_limit 3 (by decide),supercritical_limit 3 (by decide),
    Computable.encode_iff.mpr hq,hc,he⟩

end FixedClauseThreshold.Computability

end OAI
