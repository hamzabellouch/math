import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.RestrictionLocalization
import OAI.AlgebraicGeometry.Seshadri.Divisors.BaseSections

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

def chartModuleEquiv (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {N : Y.Modules} (e : M.restrict f ≅ N) :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    OpenSections (M.restrict f) ⊤ ≃ₗ[Γ(X,⊤)] OpenSections N ⊤ := by
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let E := moduleIsoSections e ⊤
  exact { E.toEquiv with
    map_add' := E.map_add
    map_smul' := fun r m => E.map_smul (f.appTop r) m }

def chartModuleMap (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {N : Y.Modules} (e : M.restrict f ≅ N) :
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    OpenSections M ⊤ →ₗ[Γ(X,⊤)] OpenSections N ⊤ := by
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  exact (chartModuleEquiv M f e).toLinearMap ∘ₗ openImmersionTop M f

theorem chartModuleMap_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] {N : Y.Modules} (e : M.restrict f ≅ N)
    (t : Γ(X,⊤)) (ht : f.opensRange = X.basicOpen t) :
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    IsLocalizedModule.Away t (chartModuleMap M f e) := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let : IsLocalizedModule.Away t (openImmersionTop M f) :=
    openImmersionTop_localize M f t ht
  exact IsLocalizedModule.of_linearEquiv (.powers t) (openImmersionTop M f)
    (chartModuleEquiv M f e)

namespace BaseSections
variable {K : Type} [CommRing K]

def chartMap (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N) :
    Sections kX M ⊤ →ₗ[K] Sections kY N ⊤ := by
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  refine { toFun := chartModuleMap M f e
           map_add' := (chartModuleMap M f e).map_add
           map_smul' := ?_ }
  intro r m
  have h := (chartModuleMap M f e).map_smul (kX r) m
  change _ = (f.appTop (kX r)) • (chartModuleMap M f e m) at h
  exact h.trans (congrArg (fun c : Γ(Y,⊤) => c • chartModuleMap M f e m)
    (RingHom.congr_fun hk r))

lemma chartMap_smul (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N)
    (r : Γ(X,⊤)) (m : Sections kX M ⊤) :
    chartMap kX kY f hk M e (r • m) = f.appTop r • chartMap kX kY f hk M e m := by
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  exact (chartModuleMap M f e).map_smul r m

end BaseSections
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
