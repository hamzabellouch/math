import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.BaseSections
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SurfaceCech

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {K : Type} [Field K] {X : Scheme.{0}}

def tripleBaseImage (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V W : X.Opens) :
    Submodule K (Sections k M (tripleOpen U V W)) :=
  ((res k M (show tripleOpen U V W ≤ U ⊓ W from inf_le_left)).range ⊔
   (res k M (show tripleOpen U V W ≤ V ⊓ W from inf_le_right)).range) ⊔
   (res k M (show tripleOpen U V W ≤ U ⊓ V from
      inf_le_inf inf_le_left inf_le_left)).range

def tripleBaseCohomologyTwo (k : K →+* Γ(X,⊤))
    (M : X.Modules) (U V W : X.Opens) (hc : (U ⊔ V) ⊔ W = ⊤) :
    letI := Module.compHom (cohomology M 2) k
    (Sections k M (tripleOpen U V W) ⧸ tripleBaseImage k M U V W) →ₗ[K]
      cohomology M 2 := by
  letI : Algebra K Γ(X,⊤) := k.toAlgebra
  letI := Module.compHom (cohomology M 2) k
  letI : IsScalarTower K Γ(X,⊤) (cohomology M 2) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  letI : Module K (OpenSections M (tripleOpen U V W)) := Module.compHom _ k
  letI : IsScalarTower K Γ(X,⊤) (OpenSections M (tripleOpen U V W)) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  have he : tripleBaseImage k M U V W = (tripleChartImage M U V W).restrictScalars K := by
    have hsup := Submodule.restrictScalars_sup K
      ((openRestriction M (show tripleOpen U V W ≤ U ⊓ W from inf_le_left)).range ⊔
       (openRestriction M (show tripleOpen U V W ≤ V ⊓ W from inf_le_right)).range)
      (openRestriction M (show tripleOpen U V W ≤ U ⊓ V from
        inf_le_inf inf_le_left inf_le_left)).range
    conv_rhs at hsup => rw [Submodule.restrictScalars_sup]
    exact hsup.symm
  let F := ((tripleCohomologyTwo M U V W hc).comp
    (tripleChartImage M U V W).mkQ).restrictScalars K
  refine (tripleBaseImage k M U V W).liftQ F ?_
  intro z hz
  have hz' : z ∈ tripleChartImage M U V W := by
    change z ∈ (tripleChartImage M U V W).restrictScalars K
    rw [← he]
    exact hz
  change tripleCohomologyTwo M U V W hc
    ((tripleChartImage M U V W).mkQ z) = 0
  rw [show (tripleChartImage M U V W).mkQ z = 0 from
    (Submodule.Quotient.mk_eq_zero _).mpr hz', map_zero]

lemma tripleBaseCohomologyTwo_surjective [IsNoetherian X] (k : K →+* Γ(X,⊤))
    (M : X.Modules) [M.IsQuasicoherent] (U V W : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hUV : IsAffineOpen (U ⊓ V)) (hUW : IsAffineOpen (U ⊓ W))
    (hVW : IsAffineOpen (V ⊓ W)) (hc : (U ⊔ V) ⊔ W = ⊤) :
    Function.Surjective (tripleBaseCohomologyTwo k M U V W hc) := by
  intro x
  obtain ⟨y,hy⟩ := tripleCohomologyTwo_surjective M U V W hU hV hW hUV hUW hVW hc x
  obtain ⟨z,rfl⟩ := (tripleChartImage M U V W).mkQ_surjective y
  refine ⟨(tripleBaseImage k M U V W).mkQ z, ?_⟩
  exact hy

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
