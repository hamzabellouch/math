import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.AffineLocalizing
import OAI.AlgebraicGeometry.Seshadri.Sheaves.RestrictedSections

namespace OAI

section
noncomputable section
                                                 
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y Z : Scheme.{0}}

def moduleIsoSections {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    OpenSections M U ≃ₗ[Γ(X,⊤)] OpenSections N U where
  toFun := e.hom.val.app (op U)
  invFun := e.inv.val.app (op U)
  left_inv m := by
    have h := congrArg (fun f : M ⟶ M => f.val.app (op U) m) e.hom_inv_id
    exact h
  right_inv m := by
    have h := congrArg (fun f : N ⟶ N => f.val.app (op U) m) e.inv_hom_id
    exact h
  map_add' := map_add _
  map_smul' r m := (e.hom.val.app (op U)).hom.map_smul (restrictScalar X U r) m

def openImmersionTop (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f] :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    OpenSections M ⊤ →ₗ[Γ(X,⊤)] OpenSections (M.restrict f) ⊤ := by
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  exact (restrictedOpenSections M f ⊤).symm.toLinearMap ∘ₗ
    openRestriction M (show f ''ᵁ ⊤ ≤ ⊤ from le_top)

theorem openImmersionTop_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] (t : Γ(X,⊤))
    (hf : f.opensRange = X.basicOpen t) :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    IsLocalizedModule.Away t (openImmersionTop M f) := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  have he : X.basicOpen t = f ''ᵁ (⊤ : Y.Opens) :=
    hf.symm.trans (Scheme.Hom.image_top_eq_opensRange f).symm
  let e := (openSectionsCongr M he).trans (restrictedOpenSections M f ⊤).symm
  let g := openRestriction M (X.basicOpen_le t)
  have : IsLocalizedModule.Away t g := affine_openRestriction_localize M t
  have h := IsLocalizedModule.of_linearEquiv (.powers t) g e
  have hp : e.toLinearMap ∘ₗ g = openImmersionTop M f := by
    ext m
    change (restrictedOpenSections M f ⊤).symm
      (openSectionsCongr M he (openRestriction M (X.basicOpen_le t) m)) = _
    rw [openSectionsCongr_restriction]
    rfl
  rwa [hp] at h

theorem openImmersionTop_denominators [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] (t : Γ(X,⊤))
    (hf : f.opensRange = X.basicOpen t) (x : OpenSections (M.restrict f) ⊤) :
    ∃ n : ℕ, ∃ y : OpenSections M ⊤,
       openImmersionTop M f y = (f.appTop (t^n)) • x := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  have : IsLocalizedModule.Away t (openImmersionTop M f) :=
    openImmersionTop_localize M f t hf
  obtain ⟨exponent, globalSection, denominator_eq⟩ :=
    IsLocalizedModule.Away.surj (openImmersionTop M f) t x
  exact ⟨exponent, globalSection, denominator_eq.symm⟩
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
