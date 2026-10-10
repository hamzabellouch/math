import OAI.Probability.SLE.Geometry.ComplexJordanExtension

namespace OAI

/-! Glue a homeomorphism on one closed piece to the identity on a second
closed piece, retaining the prescribed values on their intersection. -/
noncomputable section
open Set

namespace SLEExactGauge

def closedComplexUnionHomeomorph {A A' B : Set ℂ}
    (hA : IsClosed A) (hA' : IsClosed A') (hB : IsClosed B)
    (e : A ≃ₜ A')
    (he : ∀ x : A, (x : ℂ) ∈ B → (e x : ℂ)=x)
    (hi : ∀ x : A', (x : ℂ) ∈ B → (e.symm x : ℂ)=x) :
    ↥(A ∪ B) ≃ₜ ↥(A' ∪ B) := by
  classical
  let f (x : ℂ) := if hx : x ∈ A then (e ⟨x,hx⟩ : ℂ) else x
  let g (x : ℂ) := if hx : x ∈ A' then (e.symm ⟨x,hx⟩ : ℂ) else x
  have hfA : ContinuousOn f A := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_subtype_val.comp e.continuous using 1
    funext x
    exact dite_eq_left x.property
  have hgA : ContinuousOn g A' := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_subtype_val.comp e.symm.continuous using 1
    funext x
    exact dite_eq_left x.property
  have hfB : ContinuousOn f B := by
    apply continuousOn_id.congr
    intro x hx
    dsimp [f]
    split_ifs with ha
    · exact he ⟨x,ha⟩ hx
    · rfl
  have hgB : ContinuousOn g B := by
    apply continuousOn_id.congr
    intro x hx
    dsimp [g]
    split_ifs with ha
    · exact hi ⟨x,ha⟩ hx
    · rfl
  have hf : ContinuousOn f (A ∪ B) := hfA.union_of_isClosed hfB hA hB
  have hg : ContinuousOn g (A' ∪ B) := hgA.union_of_isClosed hgB hA' hB
  have hfm : MapsTo f (A ∪ B) (A' ∪ B) := by
    intro x hx
    dsimp [f]
    split_ifs with ha
    · exact Or.inl (e ⟨x,ha⟩).property
    · exact Or.inr (hx.resolve_left ha)
  have hgm : MapsTo g (A' ∪ B) (A ∪ B) := by
    intro x hx
    dsimp [g]
    split_ifs with ha
    · exact Or.inl (e.symm ⟨x,ha⟩).property
    · exact Or.inr (hx.resolve_left ha)
  have hgf (x : ℂ) (hx : x ∈ A ∪ B) : g (f x)=x := by
    by_cases ha : x ∈ A
    · have hfa : f x=(e ⟨x,ha⟩ : ℂ) := dite_eq_left ha
      rw [hfa]
      dsimp [g]
      rw [dite_eq_left (e ⟨x,ha⟩).property]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x,ha⟩)
    · rw [show f x=x from dite_eq_right ha]
      dsimp [g]
      split_ifs with ha'
      · exact hi ⟨x,ha'⟩ (hx.resolve_left ha)
      · rfl
  have hfg (x : ℂ) (hx : x ∈ A' ∪ B) : f (g x)=x := by
    by_cases ha : x ∈ A'
    · have hga : g x=(e.symm ⟨x,ha⟩ : ℂ) := dite_eq_left ha
      rw [hga]
      dsimp [f]
      rw [dite_eq_left (e.symm ⟨x,ha⟩).property]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x,ha⟩)
    · rw [show g x=x from dite_eq_right ha]
      dsimp [f]
      split_ifs with ha'
      · exact he ⟨x,ha'⟩ (hx.resolve_left ha)
      · rfl
  exact
    { toFun := fun x => ⟨f x,hfm x.property⟩
      invFun := fun x => ⟨g x,hgm x.property⟩
      left_inv := fun x => Subtype.ext (hgf x x.property)
      right_inv := fun x => Subtype.ext (hfg x x.property)
      continuous_toFun := (hf.comp_continuous continuous_subtype_val
        (fun x => x.property)).subtype_mk _
      continuous_invFun := (hg.comp_continuous continuous_subtype_val
        (fun x => x.property)).subtype_mk _ }

end SLEExactGauge

end

end OAI
