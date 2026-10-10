import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.RestrictedSections

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

def Sections (_ : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) := OpenSections M U
instance (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    AddCommGroup (Sections k M U) := inferInstanceAs (AddCommGroup (OpenSections M U))
instance globalModule (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module Γ(X,⊤) (Sections k M U) := inferInstanceAs (Module Γ(X,⊤) (OpenSections M U))
instance baseModule (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module K (Sections k M U) := Module.compHom (OpenSections M U) k

def res (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    Sections k M V →ₗ[K] Sections k M U where
  toFun := openRestriction M h
  map_add' := map_add _
  map_smul' r m := (openRestriction M h).map_smul (k r) m

def congr (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens} (h : U = V) :
    Sections k M U ≃ₗ[K] Sections k M V := by
  subst V
  exact LinearEquiv.refl K _

lemma congr_res (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens} (h : U = V)
    (m : Sections k M ⊤) : congr k M h (res k M (show U ≤ ⊤ from le_top) m) = res k M (show V ≤ ⊤ from le_top) m := by
  subst V
  rfl

lemma congr_naturality (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U V U' V' : X.Opens} (eU : U = U') (eV : V = V')
    (h : U ≤ V) (h' : U' ≤ V') (m : Sections k M V) :
    congr k M eU (res k M h m) = res k M h' (congr k M eV m) := by
  subst U' V'
  rfl

def restrictEquiv (k : K →+* Γ(X,⊤)) (M : X.Modules)
    (f : Y ⟶ X) [IsOpenImmersion f] (U : Y.Opens) :
    Sections (f.appTop.hom.comp k) (M.restrict f) U ≃ₗ[K]
      Sections k M (f ''ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' r m := (restrictedOpenSections M f U).map_smul (k r) m

lemma restrictEquiv_res (k : K →+* Γ(X,⊤)) (M : X.Modules)
    (f : Y ⟶ X) [IsOpenImmersion f] {U V : Y.Opens} (h : U ≤ V)
    (m : Sections (f.appTop.hom.comp k) (M.restrict f) V) :
    restrictEquiv k M f U (res _ _ h m) =
      res k M (f.image_mono h) (restrictEquiv k M f V m) := rfl

lemma chart_image_top (U : X.Opens) : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]

lemma chart_image_preimage (U V : X.Opens) : U.ι ''ᵁ U.ι ⁻¹ᵁ V = U ⊓ V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

def chartTop (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤ ≃ₗ[K] Sections k M U :=
  (restrictEquiv k M U.ι ⊤).trans (congr k M (chart_image_top U))

def chartOverlap (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V : X.Opens) :
    Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) (U.ι ⁻¹ᵁ V) ≃ₗ[K]
      Sections k M (U ⊓ V) :=
  (restrictEquiv k M U.ι (U.ι ⁻¹ᵁ V)).trans
    (congr k M (chart_image_preimage U V))

lemma chartRestriction (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V : X.Opens)
    (m : Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤) :
    chartOverlap k M U V (res _ _ le_top m) =
      res k M (show U ⊓ V ≤ U from inf_le_left) (chartTop k M U m) := by
  change congr k M (chart_image_preimage U V)
    (restrictEquiv k M U.ι (U.ι ⁻¹ᵁ V) (res _ _ le_top m)) = _
  rw [restrictEquiv_res]
  exact congr_naturality k M (chart_image_preimage U V) (chart_image_top U)
    _ _ _

end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
