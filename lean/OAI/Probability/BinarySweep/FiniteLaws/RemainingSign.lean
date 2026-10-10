import Mathlib
import OAI.Probability.BinarySweep.Conditional.Placement

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma realSign_ne_zero {X : Type*} [Fintype X] [DecidableEq X] (g : Equiv.Perm X) :
    realSign g≠0 := by
  simp [realSign]

lemma realSign_inv {X : Type*} [Fintype X] [DecidableEq X] (f : Equiv.Perm X) :
    realSign f⁻¹=(realSign f)⁻¹ := by
  have hm : realSign f⁻¹*realSign f=1 := by rw [←map_mul,inv_mul_cancel,map_one]
  calc
    realSign f⁻¹ = (realSign f⁻¹*realSign f)*(realSign f)⁻¹ := by
      rw [mul_assoc,mul_inv_cancel₀ (realSign_ne_zero f),mul_one]
    _ = _ := by rw [hm,one_mul]

lemma remaining_relative_realSign (g g₀ : ConditionalChoices H) :
    realSign ((remainingPerm H g₀.val g₀.property)⁻¹*remainingPerm H g.val g.property)=
      realSign ((gridSweep bits g₀.val)⁻¹*gridSweep bits g.val) := by
  let f := (gridSweep bits g₀.val)⁻¹*gridSweep bits g.val
  have hfix (i : Fin h) : f (H.position 0 i)=H.position 0 i := by
    change (gridSweep bits g₀.val).symm (gridSweep bits g.val (H.position 0 i))=_
    rw [gridSweep_path H g.val g.property,←gridSweep_path H g₀.val g₀.property,
      Equiv.symm_apply_apply]
  have hp (x : GridSlot bits) : f x∉Set.range (H.position 0) ↔ x∉Set.range (H.position 0) := by
    constructor
    · intro hx hi; obtain ⟨i,rfl⟩ := hi; exact hx ⟨i,hfix i |>.symm⟩
    · intro hx hi; obtain ⟨i,hi⟩ := hi
      exact hx ⟨i,f.injective ((hfix i).trans hi)⟩
  have hs := Equiv.Perm.sign_subtypePerm f (p := fun x => x∉Set.range (H.position 0)) hp (by
    intro x hx hi; obtain ⟨i,rfl⟩ := hi; exact hx (hfix i))
  have he : Equiv.Perm.subtypePerm f hp =
      (remainingPerm H g₀.val g₀.property)⁻¹*remainingPerm H g.val g.property := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change f x.val =
      (gridSweep bits g₀.val).symm
        ((freeIdentification H) ((freeIdentification H).symm
          ((remainingBijection H g.val g.property) x))).val
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he] at hs
  convert congrArg (fun u : ℤˣ => ((u:ℤ):ℝ)) hs using 1
  · unfold realSign; dsimp; congr 3
    congr 1; exact Subsingleton.elim _ _
  · rfl

theorem remaining_realSign_factor (g g₀ : ConditionalChoices H) :
    realSign (remainingPerm H g.val g.property) =
      (realSign (remainingPerm H g₀.val g₀.property)/realSign (gridSweep bits g₀.val))*
        realSign (gridSweep bits g.val) := by
  have he := remaining_relative_realSign H g g₀
  simp only [map_mul,realSign_inv] at he
  have h₀ := realSign_ne_zero (remainingPerm H g₀.val g₀.property)
  have h₁ := realSign_ne_zero (gridSweep bits g₀.val)
  field_simp [h₀,h₁] at he ⊢
  nlinarith [he]

end BinaryCoordinateSweeps

end

end OAI
