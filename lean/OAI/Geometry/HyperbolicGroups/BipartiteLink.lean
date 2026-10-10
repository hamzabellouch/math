import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

/-- A cyclic link whose steps alternate bipartition, with no two-step
backtrack, has at least four actual corners. This is a cardinality result
about the permutation orbit, not a simple-cycle field supplied by a user. -/
lemma four_le_link (p : Perm D) (a : D) (c : D → Bool)
    (hc : ∀ x, p.SameCycle a x → c (p x) ≠ c x)
    (h₂ : p (p a) ≠ a) : 4 ≤ Fintype.card {x // p.SameCycle a x} := by
  have ha₁ : p.SameCycle a (p a) := SameCycle.rfl.apply_right
  have ha₂ : p.SameCycle a (p (p a)) := ha₁.apply_right
  have ha₃ : p.SameCycle a (p (p (p a))) := ha₂.apply_right
  have hc₀ := hc a SameCycle.rfl
  have hc₁ := hc (p a) ha₁
  have hc₂ := hc (p (p a)) ha₂
  have h₀₁ : a ≠ p a := fun h => hc₀ (congrArg c h.symm)
  have h₁₂ : p a ≠ p (p a) := p.injective.ne h₀₁
  have h₂₃ : p (p a) ≠ p (p (p a)) := p.injective.ne h₁₂
  have h₀₂ : a ≠ p (p a) := Ne.symm h₂
  have h₁₃ : p a ≠ p (p (p a)) := p.injective.ne h₀₂
  have h₀₃ : a ≠ p (p (p a)) := by
    intro he
    rw [← he] at hc₂
    cases hx : c a <;> cases hy : c (p a) <;> cases hz : c (p (p a)) <;>
      simp only [hx,hy,hz,Bool.false_eq_true,Bool.true_eq_false,ne_eq,not_true_eq_false] at hc₀ hc₁ hc₂
  let g : Fin 4 → {x // p.SameCycle a x} :=
    ![⟨a,SameCycle.rfl⟩,⟨p a,ha₁⟩,⟨p (p a),ha₂⟩,⟨p (p (p a)),ha₃⟩]
  have hg : Function.Injective g := by
    intro i j he
    have he' := congrArg Subtype.val he
    fin_cases i <;> fin_cases j <;> simp_all [g]
  simpa using Fintype.card_le_of_injective g hg

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
