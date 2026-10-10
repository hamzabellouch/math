import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.AffineLineFinite

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

def LineBundle.restrict (L : LineBundle Y) (f : X ⟶ Y) [IsOpenImmersion f] : LineBundle X where
  sheaf := L.sheaf.restrict f
  locallyRankOne x := by
    obtain ⟨U,hxU,⟨e⟩⟩ := L.locallyRankOne (f x)
    let V := f ⁻¹ᵁ U
    refine ⟨V,hxU,⟨?_⟩⟩
    let e' := (Scheme.Modules.restrictFunctorComp (f ∣_ U) U.ι).app L.sheaf ≪≫
      (Scheme.Modules.restrictFunctor (f ∣_ U)).mapIso e ≪≫
      Scheme.Modules.restrictUnitIso (f ∣_ U)
    have e'' : L.sheaf.restrict (V.ι ≫ f) ≅ structureSheaf V.toScheme := by
      simpa only [V, morphismRestrict_ι, structureSheaf] using e'
    exact ((Scheme.Modules.restrictFunctorComp V.ι f).app L.sheaf).symm ≪≫ e''

theorem LineBundle.affine_sections_finite [IsAffine X] (L : LineBundle X) :
    Module.Finite Γ(X,⊤) Γ(L.sheaf,⊤) := by
  let f := X.isoSpec.inv
  let J := L.restrict f
  let R := Γ(X,⊤)
  let M := (modulesSpecToSheaf.obj J.sheaf).obj.obj (op ⊤)
  let : Module.Finite R M := J.spec_sections_finite
  let σ : R →+* Γ(X,f ''ᵁ ⊤) := (f.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let φ : M →ₛₗ[σ] Γ(L.sheaf,f ''ᵁ ⊤) := {
    toFun := (L.sheaf.restrictAppIso f ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (L.sheaf.restrictAppIso f ⊤).hom).surjective
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have h := Module.Finite.of_surjective φ hφ
  rw [hf] at h
  exact h

theorem LineBundle.affine_open_sections_finite (L : LineBundle X) (U : X.Opens)
    (hU : IsAffineOpen U) : Module.Finite Γ(X,U) Γ(L.sheaf,U) := by
  let : IsAffine U.toScheme := hU
  let J := L.restrict U.ι
  let : Module.Finite Γ(U.toScheme,⊤) Γ(J.sheaf,⊤) := J.affine_sections_finite
  let σ := (U.ι.appIso ⊤).inv.hom
  let φ : Γ(J.sheaf,⊤) →ₛₗ[σ] Γ(L.sheaf,U.ι ''ᵁ ⊤) := {
    toFun := (L.sheaf.restrictAppIso U.ι ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (L.sheaf.restrictAppIso U.ι ⊤).hom).surjective
  have h := Module.Finite.of_surjective φ hφ
  rwa [U.ι_image_top] at h
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
