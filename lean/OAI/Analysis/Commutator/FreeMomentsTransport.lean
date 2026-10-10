import Mathlib
import OAI.Analysis.Commutator.FreeMoments

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FreeMoments

variable {A B : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (U : ι → StarSubalgebra ℂ B)
  (τ : A →ₗ[ℂ] ℂ) (ρ : B →ₗ[ℂ] ℂ)
  (j : A →⋆ₐ[ℂ] B) (htrace : ∀ a,ρ (j a)=τ a)
  (hSU : ∀ i a,a∈S i → j a∈U i)

def Letter.transport (a : Letter S τ) : Letter U ρ where
  color := a.color
  val := j a.val
  mem := hSU _ _ a.mem
  centered := (htrace _).trans a.centered

lemma word_transport (w : List (Letter S τ)) :
    word (w.map (Letter.transport S U τ ρ j htrace hSU))=j (word w) := by
  induction w with
  | nil => simp
  | cons a w ih => simp only [List.map_cons,word_cons,Letter.transport,ih,map_mul]

include htrace hSU in
theorem free_of_map (hfree : Free U ρ) : Free S τ := by
  intro w hw hne
  let F := Letter.transport S U τ ρ j htrace hSU
  have hr : Reduced (w.map F) := by
    simpa only [Reduced,List.isChain_map,F,Letter.transport] using hw
  have hn : w.map F≠[] := fun h => hne (List.map_eq_nil_iff.mp h)
  have hz := hfree (w.map F) hr hn
  rw [word_transport,htrace] at hz
  exact hz

end Kadison.FreeMoments

end

end
end

end OAI
