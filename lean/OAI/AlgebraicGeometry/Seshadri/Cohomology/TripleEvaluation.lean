import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.NestedChart

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ModuleFlasque

variable {K : Type} [Field K] {X : Scheme.{0}}
local instance : Linear Γ(X,⊤) (SheafOfModules X.ringCatSheaf) := sheafLinear X

def BaseHom (_k : K →+* Γ(X,⊤)) (A B : X.Modules) := A ⟶ B
instance baseHomGroup (baseMap : K →+* Γ(X,⊤)) (source target : X.Modules) :
    AddCommGroup (BaseHom baseMap source target) :=
  Preadditive.homGroup (C := X.Modules) _ _

local instance baseHomModule (k : K →+* Γ(X,⊤)) (A B : X.Modules) :
    Module K (BaseHom k A B) := Module.compHom (A ⟶ B) k

local instance (target : X.Modules) (chart : X.Opens) :
    AddCommGroup ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  Preadditive.homGroup (C := X.Modules) _ _

local instance (target : X.Modules) (chart : X.Opens) :
    Module Γ(X,⊤) ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  sheafHomModule X _ _

instance freeBaseHomGroup (baseMap : K →+* Γ(X,⊤)) (target : X.Modules)
    (chart : X.Opens) : AddCommGroup (BaseHom baseMap (freeOpen X.ringCatSheaf chart) target) :=
  baseHomGroup baseMap _ _

instance freeBaseHomModule (baseMap : K →+* Γ(X,⊤)) (target : X.Modules)
    (chart : X.Opens) : Module K (BaseHom baseMap (freeOpen X.ringCatSheaf chart) target) :=
  baseHomModule baseMap _ _

def freeBaseEquiv (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    BaseHom k (freeOpen X.ringCatSheaf U) M ≃ₗ[K] Sections k M U where
  toEquiv := (freeOpenLinearEquiv M U).toEquiv
  map_add' := (freeOpenLinearEquiv M U).map_add
  map_smul' r m := (freeOpenLinearEquiv M U).map_smul (k r) m

def homChart (k : K →+* Γ(X,⊤)) (M : X.Modules) {U T : X.Opens} (h : T ≤ U) :
    BaseHom k (freeOpen X.ringCatSheaf U) M →ₗ[K]
      Sections (T.ι.appTop.hom.comp k) (M.restrict T.ι) ⊤ :=
  (chartTop k M T).symm.toLinearMap.comp ((res k M h).comp (freeBaseEquiv k M U).toLinearMap)

lemma homChart_natural (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V T : X.Opens}
    (h : T ≤ V) (g : V ≤ U) (f : freeOpen X.ringCatSheaf U ⟶ M) :
    homChart k M h (freeOpenMap X.ringCatSheaf (homOfLE g) ≫ f) =
      homChart k M (h.trans g) f := by
  change (chartTop k M T).symm
      (res k M h (freeBaseEquiv k M V (freeOpenMap X.ringCatSheaf (homOfLE g) ≫ f))) =
    (chartTop k M T).symm (res k M (h.trans g) (freeBaseEquiv k M U f))
  apply congrArg (chartTop k M T).symm
  change res k M h (freeOpenLinearEquiv M V (freeOpenMap X.ringCatSheaf (homOfLE g) ≫ f)) = _
  rw [freeOpenLinearEquiv_naturality]
  exact res_comp k M h g _

lemma homChart_range (k : K →+* Γ(X,⊤)) (M : X.Modules) {U T : X.Opens} (h : T ≤ U) :
    (homChart k M h).range = (chartRes k M h).range := by
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    refine ⟨(chartTop k M U).symm (freeBaseEquiv k M U f),?_⟩
    apply (chartTop k M T).injective
    rw [chartTop_nested,LinearEquiv.apply_symm_apply]
    exact ((chartTop k M T).apply_symm_apply _).symm
  · rintro _ ⟨m,rfl⟩
    refine ⟨(freeBaseEquiv k M U).symm (chartTop k M U m),?_⟩
    apply (chartTop k M T).injective
    simp only [homChart,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
    rw [chartTop_nested]

lemma homChart_injective [IsIntegral X] (k : K →+* Γ(X,⊤)) (L : LineBundle X)
    {U T : X.Opens} (h : T ≤ U) [Nonempty T] : Function.Injective (homChart k L.sheaf h) := by
  intro f g he
  apply (freeBaseEquiv k L.sheaf U).injective
  apply L.restriction_injective (homOfLE h)
  change res k L.sheaf h (freeBaseEquiv k L.sheaf U f) = res k L.sheaf h (freeBaseEquiv k L.sheaf U g)
  exact (chartTop k L.sheaf T).symm.injective he

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
