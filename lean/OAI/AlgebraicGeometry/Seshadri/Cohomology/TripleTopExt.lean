import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.TripleExt

namespace OAI


                                      
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque ModuleMayerVietoris

variable {X : Scheme.{0}}
local instance tripleTopExtLinear : Linear Γ(X,⊤) X.Modules := sheafLinear X
local instance tripleTopExtHasExt : HasExt.{1} X.Modules := schemeHasExt

def tripleTopHomExtEquiv [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hc : (U ⊔ V) ⊔ W = ⊤) :
    let complex : ShortComplex X.Modules :=
      tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
    ((complex.X₁ ⟶ M) ⧸ (Linear.leftComp Γ(X,⊤) M complex.f).range) ≃ₗ[Γ(X,⊤)]
      cohomology M 1 := by
  let complex : ShortComplex X.Modules :=
    tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
  let topIso : complex.X₃ ≅ structureSheaf X :=
    eqToIso (congrArg (FiniteCoverCohomology.freeOpenModule (X := X)) hc) ≪≫
      FreeOpenUnit.freeTopIso X.ringCatSheaf
  exact (tripleHomExtEquiv (X := X) M U V W hU hV hW).trans
    (extSourceIso (X := X) topIso M 1)

def tripleTopHomCohomologyOne [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hc : (U ⊔ V) ⊔ W = ⊤) :
    let complex : ShortComplex X.Modules :=
      tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
    (complex.X₁ ⟶ M) →ₗ[Γ(X,⊤)] cohomology M 1 := by
  let complex : ShortComplex X.Modules :=
    tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
  exact (tripleTopHomExtEquiv (X := X) M U V W hU hV hW hc).toLinearMap.comp
    (Linear.leftComp Γ(X,⊤) M complex.f).range.mkQ

lemma tripleTopHomCohomologyOne_surjective [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hc : (U ⊔ V) ⊔ W = ⊤) : Function.Surjective
      (tripleTopHomCohomologyOne M U V W hU hV hW hc) :=
  (tripleTopHomExtEquiv (X := X) M U V W hU hV hW hc).surjective.comp
    (Submodule.mkQ_surjective _)

lemma tripleTopHomCohomologyOne_zero [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hc : (U ⊔ V) ⊔ W = ⊤) :
    let complex : ShortComplex X.Modules :=
      tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
    ∀ (x : complex.X₁ ⟶ M),
      x ∈ (Linear.leftComp Γ(X,⊤) M complex.f).range →
      tripleTopHomCohomologyOne M U V W hU hV hW hc x = 0 := by
  intro complex relation inRange
  let quotientEquiv := tripleTopHomExtEquiv (X := X) M U V W hU hV hW hc
  have class_zero : (Linear.leftComp Γ(X,⊤) M complex.f).range.mkQ relation = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr inRange
  exact (congrArg quotientEquiv class_zero).trans quotientEquiv.map_zero
end
end MaximalSeshadri.Geometry

end

end OAI
