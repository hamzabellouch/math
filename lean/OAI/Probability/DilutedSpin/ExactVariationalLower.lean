import OAI.Probability.DilutedSpin.CenteredTrialLocal
import OAI.Probability.DilutedSpin.SymmetricTrialLower
import OAI.Probability.DilutedSpin.UpperTrial

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter

lemma admissible_trial_lower {q : ℕ} (M : Model (q+1)) (hM : Admissible M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ),Exponents m ∧
      functional M r ζ m ≤ liminf (pressure M) atTop+ε := by
  obtain ⟨r,ζ,m,hm,hl⟩ := symmetric_trial_lower (centeredModel M) hM.density
    (centeredModel_interaction_integrable M hM.interaction_integrable)
    (centeredModel_field_integrable M hM.field_integrable) (centeredModel_symmetric M hM) hε
  rw [functional_center M (by omega) m (fun i => (hm.2 i).1) ζ
    hM.interaction_integrable hM.field_integrable,
    liminf_pressure_center M hM.interaction_integrable hM.field_integrable] at hl
  exact ⟨r,ζ,m,hm,by linarith⟩

lemma variationalValue_le_liminf_pressure {p : ℕ} (M : Model p) (hM : Admissible M) :
    variationalValue M ≤ liminf (pressure M) atTop := by
  have hp : p=(p-1)+1 := by have := hM.arity; omega
  revert M
  rw [hp]
  intro M hM
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r,ζ,m,hm,hl⟩ := admissible_trial_lower M hM hε
  exact (variationalValue_le_functional_integrable M hM.interaction_integrable hM.field_integrable r ζ m hm).trans hl
end DilutedSpinGlass

end

end OAI
