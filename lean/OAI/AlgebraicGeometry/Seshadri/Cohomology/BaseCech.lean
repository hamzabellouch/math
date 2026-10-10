import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.CurveCech
import OAI.AlgebraicGeometry.Seshadri.Geometry.PencilCokernel

namespace OAI

section
noncomputable section
                                  
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {K : Type} [Field K] {X : Scheme.{0}}

def twoBaseCohomologyOne [IsNoetherian X] (k : K →+* Γ(X,⊤))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hc : U ⊔ V = ⊤) :
    letI := Module.compHom (cohomology M 1) k
    (Sections k M (U ⊓ V) ⧸ twoBaseImage k M U V) ≃ₗ[K] cohomology M 1 := by
  letI : Algebra K Γ(X,⊤) := k.toAlgebra
  letI := Module.compHom (cohomology M 1) k
  letI : IsScalarTower K Γ(X,⊤) (cohomology M 1) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  letI : Module K (OpenSections M (U ⊓ V)) := Module.compHom _ k
  letI : IsScalarTower K Γ(X,⊤) (OpenSections M (U ⊓ V)) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  let baseImage : Submodule K (OpenSections M (U ⊓ V)) := twoBaseImage k M U V
  have he : baseImage = (twoChartImage M U V).restrictScalars K := by
    apply Submodule.ext
    intro x
    have baseMem := Submodule.mem_sup (R := K) (M := Sections k M (U ⊓ V))
      (p := (res k M (show U ⊓ V ≤ U from inf_le_left)).range)
      (p' := (res k M (show U ⊓ V ≤ V from inf_le_right)).range) (x := x)
    have chartMem := Submodule.mem_sup (R := Γ(X,⊤)) (M := OpenSections M (U ⊓ V))
      (p := (openRestriction M (show U ⊓ V ≤ U from inf_le_left)).range)
      (p' := (openRestriction M (show U ⊓ V ≤ V from inf_le_right)).range) (x := x)
    exact baseMem.trans chartMem.symm
  let E := Submodule.Quotient.restrictScalarsEquiv K (twoChartImage M U V)
  let F := (twoAffineCohomologyOne M U V hU hV hc).restrictScalars K
  exact (Submodule.quotEquivOfEq _ _ he).trans (E.trans F)
end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
