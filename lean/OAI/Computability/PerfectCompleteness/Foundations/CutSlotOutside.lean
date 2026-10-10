import OAI.Computability.PerfectCompleteness.Foundations.CutSlotAssembly

namespace OAI

section

namespace PerfectCompleteness.CutSlotAssembly

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces

variable {branch : Nat → Nat} {n m : Nat} {V : Type*}

theorem fill_outside (p : Path branch n m)
    (outside : Slots branch n → V) (inside : Slots branch m → V)
    (s : Slots branch n) (hs : s ∉ Set.range p.slotEmbedding) :
    fill p outside inside s = outside s := by
  revert outside inside s hs
  induction p with
  | refl _ =>
      intro outside inside s hs
      exact False.elim (hs ⟨s, rfl⟩)
  | step i p ih =>
      intro outside inside s hs
      obtain ⟨j, s⟩ := s
      by_cases hji : j = i
      · subst j
        have htail : s ∉ Set.range p.slotEmbedding := by
          rintro ⟨a, ha⟩
          apply hs
          exact ⟨a, congrArg (fun b => (i, b)) ha⟩
        simpa only [fill, ite_eq_left rfl, ite_true] using
          ih (fun b => outside (i, b)) inside s htail
      · simp only [fill, ite_eq_right hji]

theorem fill_outside_eq (p : Path branch n m)
    (outside : Slots branch n → V) (left right : Slots branch m → V)
    (s : Slots branch n) (hs : s ∉ Set.range p.slotEmbedding) :
    fill p outside left s = fill p outside right s := by
  rw [fill_outside p outside left s hs, fill_outside p outside right s hs]

end
end PerfectCompleteness.CutSlotAssembly

end

end OAI
