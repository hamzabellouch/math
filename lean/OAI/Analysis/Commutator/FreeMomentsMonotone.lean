import Mathlib
import OAI.Analysis.Commutator.FreeMoments

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FreeMoments

variable {A ι : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {S T : ι → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

lemma Free.mono (hfree : Free T τ) (hle : ∀ i,S i≤T i) : Free S τ := by
  let f : Letter S τ → Letter T τ := fun a => ⟨a.color,a.val,hle _ a.mem,a.centered⟩
  intro w hw hne
  have hr : Reduced (w.map f) := (List.isChain_map _).mpr hw
  have hn : w.map f≠[] := by
    cases w with
    | nil => exact (hne rfl).elim
    | cons a w => intro h; cases h
  have h := hfree (w.map f) hr hn
  simpa only [word,List.map_map,Function.comp_def] using h

end Kadison.FreeMoments

end

end
end

end OAI
