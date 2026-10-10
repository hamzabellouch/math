import OAI.MeasureTheory.Falconer.Shells.NormalizedHighShellError

namespace OAI

namespace PlanarFalconer
open MeasureTheory

theorem list_sum_measurable_bounded {ι : Type*} (L : List ι) (F : ι → ℝ → ℂ)
    (hF : ∀ i ∈ L, Measurable (F i) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖F i r‖ ≤ C) :
    Measurable (fun r => (L.map (fun i => F i r)).sum) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖(L.map (fun i => F i r)).sum‖ ≤ C := by
  induction L with
  | nil => exact ⟨by simp,
      0,le_rfl,by simp⟩
  | cons a L ih =>
    obtain ⟨ha,A,hA,hAb⟩ := hF a (by simp)
    obtain ⟨hl,D,hD,hDb⟩ := ih (fun i hi => hF i (by simp [hi]))
    refine ⟨?_,A+D,add_nonneg hA hD,?_⟩
    · exact ha.add hl
    intro r
    simpa using (norm_add_le (F a r) ((L.map (fun i => F i r)).sum)).trans
      (add_le_add (hAb r) (hDb r))

end PlanarFalconer

end OAI
