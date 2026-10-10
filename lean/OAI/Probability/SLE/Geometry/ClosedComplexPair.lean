import OAI.Probability.SLE.Geometry.ClosedComplexUnion

namespace OAI

/-! Gluing two prescribed homeomorphisms on closed pieces. -/
noncomputable section
open Set

namespace SLEExactGauge

def closedComplexPairHomeomorph {A A' B B' : Set ℂ}
    (hA : IsClosed A) (hA' : IsClosed A') (hB : IsClosed B) (hB' : IsClosed B')
    (e : A ≃ₜ A') (d : B ≃ₜ B')
    (he : ∀ (x : A) (hx : (x:ℂ) ∈ B), (e x:ℂ)=d ⟨x,hx⟩)
    (hi : ∀ (x : A') (hx : (x:ℂ) ∈ B'), (e.symm x:ℂ)=d.symm ⟨x,hx⟩) :
    ↥(A ∪ B) ≃ₜ ↥(A' ∪ B') := by
  classical
  let f (x : ℂ) := if ha : x ∈ A then (e ⟨x,ha⟩:ℂ)
    else if hb : x ∈ B then (d ⟨x,hb⟩:ℂ) else x
  let g (x : ℂ) := if ha : x ∈ A' then (e.symm ⟨x,ha⟩:ℂ)
    else if hb : x ∈ B' then (d.symm ⟨x,hb⟩:ℂ) else x
  have hfA (x : A) : f x=(e x:ℂ) := by simp only [f,dite_eq_left x.property]
  have hfB (x : B) : f x=(d x:ℂ) := by
    dsimp [f]
    by_cases ha : (x:ℂ) ∈ A
    · rw [dite_eq_left ha]
      exact he ⟨x,ha⟩ x.property
    · rw [dite_eq_right ha,dite_eq_left x.property]
  have hgA (x : A') : g x=(e.symm x:ℂ) := by simp only [g,dite_eq_left x.property]
  have hgB (x : B') : g x=(d.symm x:ℂ) := by
    dsimp [g]
    by_cases ha : (x:ℂ) ∈ A'
    · rw [dite_eq_left ha]
      exact hi ⟨x,ha⟩ x.property
    · rw [dite_eq_right ha,dite_eq_left x.property]
  have hfAc : ContinuousOn f A := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp e.continuous).congr (fun x => (hfA x).symm)
  have hfBc : ContinuousOn f B := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp d.continuous).congr (fun x => (hfB x).symm)
  have hgAc : ContinuousOn g A' := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp e.symm.continuous).congr (fun x => (hgA x).symm)
  have hgBc : ContinuousOn g B' := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp d.symm.continuous).congr (fun x => (hgB x).symm)
  have hfm : MapsTo f (A ∪ B) (A' ∪ B') := by
    intro x hx
    rcases hx with hx|hx
    · rw [hfA ⟨x,hx⟩]; exact Or.inl (e ⟨x,hx⟩).property
    · rw [hfB ⟨x,hx⟩]; exact Or.inr (d ⟨x,hx⟩).property
  have hgm : MapsTo g (A' ∪ B') (A ∪ B) := by
    intro x hx
    rcases hx with hx|hx
    · rw [hgA ⟨x,hx⟩]; exact Or.inl (e.symm ⟨x,hx⟩).property
    · rw [hgB ⟨x,hx⟩]; exact Or.inr (d.symm ⟨x,hx⟩).property
  have hgf (x : ℂ) (hx : x ∈ A ∪ B) : g (f x)=x := by
    rcases hx with hx|hx
    · rw [hfA ⟨x,hx⟩,hgA (e ⟨x,hx⟩)]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x,hx⟩)
    · rw [hfB ⟨x,hx⟩,hgB (d ⟨x,hx⟩)]
      exact congrArg Subtype.val (d.symm_apply_apply ⟨x,hx⟩)
  have hfg (x : ℂ) (hx : x ∈ A' ∪ B') : f (g x)=x := by
    rcases hx with hx|hx
    · rw [hgA ⟨x,hx⟩,hfA (e.symm ⟨x,hx⟩)]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)
    · rw [hgB ⟨x,hx⟩,hfB (d.symm ⟨x,hx⟩)]
      exact congrArg Subtype.val (d.apply_symm_apply ⟨x,hx⟩)
  exact
    { toFun := fun x => ⟨f x,hfm x.property⟩
      invFun := fun x => ⟨g x,hgm x.property⟩
      left_inv := fun x => Subtype.ext (hgf x x.property)
      right_inv := fun x => Subtype.ext (hfg x x.property)
      continuous_toFun := ((hfAc.union_of_isClosed hfBc hA hB).comp_continuous
        continuous_subtype_val (fun x => x.property)).subtype_mk _
      continuous_invFun := ((hgAc.union_of_isClosed hgBc hA' hB').comp_continuous
        continuous_subtype_val (fun x => x.property)).subtype_mk _ }

end SLEExactGauge

end

end OAI
