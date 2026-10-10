import OAI.NumberTheory.PiExponent.Ampleness.BlowupIdeal

namespace OAI

namespace PiExponent.GeometrySupport.AffineIdealSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule PiExponentSeshadri.IdealPullback
variable {R : Type} [CommRing R] (A : Ideal R)

def value (s : Γ(closedModule (specIdeal A), ⊤)) : R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom
    ((closedInclusion (specIdeal A)).app ⊤ s)

theorem value_mem (s : Γ(closedModule (specIdeal A), ⊤)) : value A s ∈ A := by
  have hs : (closedInclusion (specIdeal A)).app ⊤ s ∈
      A.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    rw [← specIdeal_top A, ← closed_image (specIdeal A) ⟨⊤, isAffineOpen_top _⟩]
    exact ⟨s,rfl⟩
  obtain ⟨a,ha,he⟩ := (Ideal.mem_map_iff_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective).mp hs
  unfold value
  rw [← he, ← CommRingCat.comp_apply, Iso.inv_hom_id]
  exact ha

def toIdeal : Γ(closedModule (specIdeal A), ⊤) →+ A where
  toFun s := ⟨value A s, value_mem A s⟩
  map_zero' := by
    apply Subtype.ext
    change value A 0 = 0
    simp [value]
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.map_zero
  map_add' s t := by
    apply Subtype.ext
    change value A (s+t) = value A s + value A t
    simp [value]
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.map_add _ _

theorem toIdeal_injective : Function.Injective (toIdeal A) := by
  intro s t h
  have hh : value A s = value A t := congrArg Subtype.val h
  have hv := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom).injective hh
  let : Mono (closedInclusion (specIdeal A)) :=
    inferInstanceAs (Mono (inclusion (specIdeal A).subschemeι))
  let : Mono (closedInclusion (specIdeal A)).val := inferInstanceAs
    (Mono ((Scheme.Modules.toPresheafOfModules (Spec (CommRingCat.of R))).map
      (closedInclusion (specIdeal A))))
  exact PresheafOfModules.injective_of_mono
    (closedInclusion (specIdeal A)).val (op ⊤) hv

theorem toIdeal_surjective : Function.Surjective (toIdeal A) := by
  intro a
  have ha : (Scheme.ΓSpecIso (CommRingCat.of R)).inv a.val ∈
      (specIdeal A).ideal ⟨⊤,isAffineOpen_top _⟩ := by
    rw [specIdeal_top]
    exact Ideal.mem_map_of_mem _ a.property
  rw [← closed_image] at ha
  obtain ⟨s,hs⟩ := ha
  change (closedInclusion (specIdeal A)).app ⊤ s =
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv a.val at hs
  refine ⟨s,?_⟩
  apply Subtype.ext
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
    ((closedInclusion (specIdeal A)).app ⊤ s) = a.val
  rw [hs, ← CommRingCat.comp_apply, Iso.inv_hom_id]
  rfl

def equiv : Γ(closedModule (specIdeal A), ⊤) ≃+ A :=
  AddEquiv.ofBijective (toIdeal A) ⟨toIdeal_injective A, toIdeal_surjective A⟩

@[simp] theorem equiv_inclusion (s : Γ(closedModule (specIdeal A), ⊤)) :
    (equiv A s).val = (Scheme.ΓSpecIso (CommRingCat.of R)).hom
      ((closedInclusion (specIdeal A)).app ⊤ s) := rfl

@[simp] theorem equiv_symm_inclusion (a : A) :
    (closedInclusion (specIdeal A)).app ⊤ ((equiv A).symm a) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv a.val := by
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom).injective
  rw [← equiv_inclusion, AddEquiv.apply_symm_apply,
    ← CommRingCat.comp_apply, Iso.inv_hom_id]
  rfl

end
end PiExponent.GeometrySupport.AffineIdealSections

end OAI
