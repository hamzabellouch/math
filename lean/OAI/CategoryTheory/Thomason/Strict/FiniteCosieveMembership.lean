import OAI.CategoryTheory.Thomason.Simplicial.PosetSieveNaturality
import OAI.CategoryTheory.Thomason.Transfer.FiniteStreetSievePushouts

namespace OAI

section

/-! # The actual Street image of a finite-dimensional cosieve -/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

theorem cosieveMembershipLabel_object {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsUpperSet A)
    (x : Objects ((r.categorification h).obj (nerve P)).val) :
    (r.membershipLabel h Aᶜ hA.compl).toFun x.val = StrictPoset.identity 1 ↔
      r.posetObjectsEquiv h P x ∈ A := by
  change (StrictPoset.map (cosieveCharacteristic A hA)).toFun
    ((r.posetEvaluation h P).toFun x.val) = _ ↔ _
  rw [r.posetEvaluation_object h x, StrictPoset.map_identity]
  constructor
  · intro he
    exact (cosieveCharacteristic_one_iff A hA _).mp
      (congrArg StrictPoset.Cell.first he)
  · intro hx
    exact congrArg StrictPoset.identity ((cosieveCharacteristic_one_iff A hA _).mpr hx)

theorem cosieveMembershipLabel_inter {P : Type} [PartialOrder P]
    (A B : Set P) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    minLabel (r.membershipLabel h Aᶜ hA.compl) (r.membershipLabel h Bᶜ hB.compl) =
      r.membershipLabel h (A ∩ B)ᶜ (hA.inter hB).compl := by
  apply Hom.ext
  funext x
  apply StrictPoset.Cell.ext
  · exact (cosieveCharacteristic_inter A B hA hB ((r.posetEvaluation h P).toFun x).first).symm
  · exact (cosieveCharacteristic_inter A B hA hB ((r.posetEvaluation h P).toFun x).last).symm

/-- Finite reflection identifies the literal inclusion's Street image with
the full one-fibre subcomplex. -/
theorem posetCosieveStreet_range {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsUpperSet A) :
    SSet.Subcomplex.range ((h.finiteStreetNerve (n+1)).map
      (r.reflect.map (h.posetMap (subposetInclusion A)))) =
      h.fiberStreetSubcomplex (r.membershipLabel h Aᶜ hA.compl) 1 := by
  let e : ((r.categorification h).obj (nerve A)).val ≅
      labelFiber (r.membershipLabel h Aᶜ hA.compl) 1 :=
    (StrictOmegaCategory.inclusion (n+1)).mapIso (r.posetCosieveIso h A hA)
  have he : (h.finiteStreetNerve (n+1)).map (r.reflect.map (h.posetMap (subposetInclusion A))) =
      h.streetNerve.map (e.hom ≫ labelFiberInclusion (r.membershipLabel h Aᶜ hA.compl) 1) :=
    congrArg h.streetNerve.map (r.posetCosieveIso_inclusion h A hA).symm
  rw [he]
  exact h.street_endpoint_factor_range 1 _ e.hom

/-- The actual finite-dimensional cosieve nerve map is monomorphic. -/
theorem posetCosieve_nerve_mono {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsUpperSet A) :
    Mono ((h.finiteStreetNerve (n+1)).map
      (r.reflect.map (h.posetMap (subposetInclusion A)))) := by
  let e : ((r.categorification h).obj (nerve A)).val ≅
      labelFiber (r.membershipLabel h Aᶜ hA.compl) 1 :=
    (StrictOmegaCategory.inclusion (n+1)).mapIso (r.posetCosieveIso h A hA)
  have he : (h.finiteStreetNerve (n+1)).map (r.reflect.map (h.posetMap (subposetInclusion A))) =
      h.streetNerve.map (e.hom ≫ labelFiberInclusion (r.membershipLabel h Aᶜ hA.compl) 1) :=
    congrArg h.streetNerve.map (r.posetCosieveIso_inclusion h A hA).symm
  rw [he]
  exact h.street_endpoint_factor_mono 1 _ e.hom

/-- The actual composite N c takes this two-cosieve square to a pushout. -/
theorem street_cosieve_maps_isPushout
    {P : Type} [PartialOrder P]
    (A B : Set P) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hcover : ∀ x, x ∈ A ∨ x ∈ B) :
    IsPushout ((r.categorification h ⋙ h.finiteStreetNerve (n+1)).map
        (nerveMap (interLeft A B).monotone.functor))
      ((r.categorification h ⋙ h.finiteStreetNerve (n+1)).map
        (nerveMap (interRight A B).monotone.functor))
      ((h.finiteStreetNerve (n+1)).map (r.reflect.map (h.posetMap (subposetInclusion A))))
      ((h.finiteStreetNerve (n+1)).map (r.reflect.map (h.posetMap (subposetInclusion B)))) := by
  let F := r.categorification h ⋙ h.finiteStreetNerve (n+1)
  have hi : F.map (nerveMap (interLeft A B).monotone.functor) ≫
      F.map (nerveMap (subposetInclusion A).monotone.functor) =
      F.map (nerveMap (subposetInclusion (A ∩ B)).monotone.functor) := by
    rw [← F.map_comp, ← orderNerveMap_comp]
    rfl
  have hj : F.map (nerveMap (interRight A B).monotone.functor) ≫
      F.map (nerveMap (subposetInclusion B).monotone.functor) =
      F.map (nerveMap (subposetInclusion (A ∩ B)).monotone.functor) := by
    rw [← F.map_comp, ← orderNerveMap_comp]
    rfl
  have : Mono (F.map (nerveMap (subposetInclusion A).monotone.functor)) :=
    r.posetCosieve_nerve_mono h A hA
  have : Mono (F.map (nerveMap (subposetInclusion B).monotone.functor)) :=
    r.posetCosieve_nerve_mono h B hB
  have : Mono (F.map (nerveMap (subposetInclusion (A ∩ B)).monotone.functor)) :=
    r.posetCosieve_nerve_mono h (A ∩ B) (hA.inter hB)
  have : Mono (F.map (nerveMap (interLeft A B).monotone.functor) ≫
      F.map (nerveMap (subposetInclusion A).monotone.functor)) := by rwa [hi]
  have hrange (S : Set P) (hS : IsUpperSet S) :
      SSet.Subcomplex.range (F.map (nerveMap (subposetInclusion S).monotone.functor)) =
        h.fiberStreetSubcomplex (r.membershipLabel h Sᶜ hS.compl) 1 := r.posetCosieveStreet_range h S hS
  apply simplicial_isPushout_of_ranges _ _ _ _ (hi.trans hj.symm)
  · rw [hrange A hA, hrange B hB]
    apply h.cosieve_street_cover
    intro x
    exact (hcover (r.posetObjectsEquiv h P x)).imp
      ((r.cosieveMembershipLabel_object h A hA x).mpr)
      ((r.cosieveMembershipLabel_object h B hB x).mpr)
  · rw [hi, hrange (A ∩ B) (hA.inter hB), hrange A hA, hrange B hB,
      ← r.cosieveMembershipLabel_inter h A B hA hB, h.fiberStreetSubcomplex_min]
    rfl

end Thomason.Construction.FiniteReflectionInput

end

section

/-! # Cellwise membership in finite-dimensional full cosieves -/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

theorem cosieveMembershipLabel_one_iff {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsUpperSet A) (x : ((r.categorification h).obj (nerve P)).val) :
    (r.membershipLabel h Aᶜ hA.compl).toFun x = StrictPoset.identity 1 ↔
      r.posetObjectsEquiv h P (((r.categorification h).obj (nerve P)).val.boundaryObject false x) ∈ A ∧
      r.posetObjectsEquiv h P (((r.categorification h).obj (nerve P)).val.boundaryObject true x) ∈ A :=
  (fullCell_label_iff (r.membershipLabel h Aᶜ hA.compl) 1 x).symm.trans
    (and_congr
      (r.cosieveMembershipLabel_object h A hA
        (((r.categorification h).obj (nerve P)).val.boundaryObject false x))
      (r.cosieveMembershipLabel_object h A hA
        (((r.categorification h).obj (nerve P)).val.boundaryObject true x)))

/-- A reflected monotone map landing in a cosieve lands in its full one
fibre on all cells. -/
theorem posetMap_cosieveMembership_one {E P : Type} [PartialOrder E] [PartialOrder P]
    (A : Set P) (hA : IsUpperSet A) (f : E →o P) (hf : ∀ x, f x ∈ A)
    (x : ((r.categorification h).obj (nerve E)).val) :
    (r.membershipLabel h Aᶜ hA.compl).toFun ((r.reflect.map (h.posetMap f)).toFun x) =
      StrictPoset.identity 1 := by
  apply (r.cosieveMembershipLabel_one_iff h A hA _).mpr
  let f' : ((r.categorification h).obj (nerve E)).val ⟶
      ((r.categorification h).obj (nerve P)).val := r.reflect.map (h.posetMap f)
  have hb (b : Bool) : r.posetObjectsEquiv h P
      (((r.categorification h).obj (nerve P)).val.boundaryObject b (f'.toFun x)) ∈ A := by
    have he := congrArg (r.posetObjectsEquiv h P) (f'.object_boundary b x)
    have hn := r.posetObjectsEquiv_naturality h f
      (((r.categorification h).obj (nerve E)).val.boundaryObject b x)
    exact (congrArg (fun z => z ∈ A) (he.symm.trans hn)).mpr (hf _)
  exact ⟨hb false, hb true⟩

end Thomason.Construction.FiniteReflectionInput

end

end OAI
