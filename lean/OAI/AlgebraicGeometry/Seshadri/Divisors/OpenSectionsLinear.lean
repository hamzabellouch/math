import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Model
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SheafExactness

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ModuleFlasque

variable {X : Scheme.{0}}

def OpenSections (M : X.Modules) (U : X.Opens) := Γ(M,U)
instance (M : X.Modules) (U : X.Opens) : AddCommGroup (OpenSections M U) :=
  inferInstanceAs (AddCommGroup Γ(M,U))
instance (M : X.Modules) (U : X.Opens) : Module Γ(X,⊤) (OpenSections M U) :=
  Module.compHom Γ(M,U) (restrictScalar X U)

local instance (M : X.Modules) (U : X.Opens) :
    AddCommGroup ((freeOpen X.ringCatSheaf U : X.Modules) ⟶ M) :=
  Preadditive.homGroup (C := X.Modules) _ _

local instance (M : X.Modules) (U : X.Opens) :
    Module Γ(X,⊤) ((freeOpen X.ringCatSheaf U : X.Modules) ⟶ M) :=
  sheafHomModule X _ _

def freeOpenLinearEquiv (M : X.Modules) (U : X.Opens) :
    ((freeOpen X.ringCatSheaf U : X.Modules) ⟶ M) ≃ₗ[Γ(X,⊤)] OpenSections M U where
  toEquiv := freeOpenEquiv X.ringCatSheaf M U
  map_add' := by intro f g; rfl
  map_smul' := by intro r f; rfl

def openRestriction (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    OpenSections M V →ₗ[Γ(X,⊤)] OpenSections M U where
  toFun := M.val.map (homOfLE h).op
  map_add' := map_add _
  map_smul' := by
    intro scalar value
    change Γ(M,V) at value
    let : Module Γ(X,V) Γ(M,V) := (M.val.obj (op V)).isModule
    let : Module Γ(X,U) Γ(M,U) := (M.val.obj (op U)).isModule
    change M.presheaf.map (homOfLE h).op (restrictScalar X V scalar • value) =
      restrictScalar X U scalar • M.presheaf.map (homOfLE h).op value
    exact (M.map_smul (homOfLE h) (restrictScalar X V scalar) value).trans
      (congrArg (fun coefficient : Γ(X,U) =>
        coefficient • M.presheaf.map (homOfLE h).op value)
        (restrictScalar_naturality X (homOfLE h) scalar))

lemma freeOpenLinearEquiv_naturality (M : X.Modules) {U V : X.Opens} (h : U ≤ V)
    (f : (freeOpen X.ringCatSheaf V : X.Modules) ⟶ M) :
    freeOpenLinearEquiv M U (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ f) =
      openRestriction M h (freeOpenLinearEquiv M V f) :=
  freeOpenEquiv_naturality X.ringCatSheaf M _ f

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
