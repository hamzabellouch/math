import OAI.NumberTheory.Ostmann.Characters.BinaryPriorSupport
import OAI.NumberTheory.Ostmann.Characters.TemplateWords

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
open BinaryPriorExposure
attribute [local instance] Classical.propDecidable

theorem wordTreeEquiv_map {α β:Type*} (f:α→β) (k j:ℕ) (p:List Bool)
    (x:WordSlot k j→α) :
    wordTreeEquiv (G:=β) k j (fun i=>f (x i))=
      BinaryPriorExposure.map (fun _=>f) j p (wordTreeEquiv (G:=α) k j x) := by
  induction j generalizing p with
  | zero => rfl
  | succ j ih =>
    change (wordTreeEquiv (G:=β) k j _,wordTreeEquiv (G:=β) k j _)=_
    apply Prod.ext
    · exact ih (false::p) _
    · exact ih (true::p) _

theorem wordTreeEquiv_allLeaves {α:Type*} (P:α→Prop) (k j:ℕ) (p:List Bool)
    (x:WordSlot k j→α) :
    AllLeaves (fun _=>P) j p (wordTreeEquiv (G:=α) k j x) ↔ ∀i,P (x i) := by
  induction j generalizing p with
  | zero =>
    constructor
    · intro h i
      have hi := initial_word_unique k i
      have he : i=⟨(.word,true),by simp [schedule,initial,InitialRole.role]⟩ := Subtype.ext hi
      change P (x ⟨(.word,true),by simp [schedule,initial,InitialRole.role]⟩) at h
      simpa only [he] using h
    · intro h
      exact h _
  | succ j ih =>
    change (AllLeaves _ j _ (wordTreeEquiv (G:=α) k j _) ∧
      AllLeaves _ j _ (wordTreeEquiv (G:=α) k j _)) ↔ _
    rw [ih,ih]
    constructor
    · rintro ⟨hl,hr⟩ i
      obtain ⟨u,b,he⟩ : ∃u b,(wordEquiv (schedule k j) j).symm (u,b)=i := by
        exact ⟨_,_,(wordEquiv (schedule k j) j).symm_apply_apply i⟩
      subst i
      cases b
      · exact hr u
      · exact hl u
    · intro h
      exact ⟨fun i=>h _,fun i=>h _⟩

end Ostmann.Characters.Template

end

end OAI
