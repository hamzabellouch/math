import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.TripleComplex

namespace OAI


                                   
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque ModuleMayerVietoris

variable {X : Scheme.{0}}
local instance tripleExtLinear : Linear Γ(X,⊤) X.Modules := sheafLinear X
local instance tripleExtHasExt : HasExt.{1} X.Modules := schemeHasExt

def tripleHomExtEquiv [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    let complex : ShortComplex X.Modules :=
      tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
    ((complex.X₁ ⟶ M) ⧸ (Linear.leftComp Γ(X,⊤) M complex.f).range) ≃ₗ[Γ(X,⊤)]
      Ext.{1} (C := X.Modules) complex.X₃ M 1 := by
  let complex : ShortComplex X.Modules :=
    tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
  let exactness : complex.ShortExact :=
    tripleKernelComplex_shortExact (X := X.carrier) X.ringCatSheaf U V W
  refine ExtCokernel.quotientEquiv (C := X.Modules) (K := Γ(X,⊤))
    (S := complex) exactness M ?_
  change ∀ middleClass : Ext.{1} (C := X.Modules)
    (FiniteCoverCohomology.freeOpenModule U ⊞
      (FiniteCoverCohomology.freeOpenModule V ⊞ FiniteCoverCohomology.freeOpenModule W))
    M 1, middleClass = 0
  intro middleClass
  apply (Ext.biprodAddEquiv (C := X.Modules)).injective
  apply Prod.ext
  · simpa only [map_zero,Ext.biprodAddEquiv_apply_fst,Prod.fst_zero] using
       FiniteCoverCohomology.affine_open_ext_zero (X := X) U hU M 0
        ((Ext.mk₀ biprod.inl).comp middleClass (zero_add _))
  · have h (z : Ext.{1} (C := X.Modules)
        (FiniteCoverCohomology.freeOpenModule V ⊞ FiniteCoverCohomology.freeOpenModule W)
        M 1) : z = 0 := by
      apply (Ext.biprodAddEquiv (C := X.Modules)).injective
      apply Prod.ext
      · simpa only [map_zero,Ext.biprodAddEquiv_apply_fst,Prod.fst_zero] using
           FiniteCoverCohomology.affine_open_ext_zero (X := X) V hV M 0
            ((Ext.mk₀ biprod.inl).comp z (zero_add _))
      · simpa only [map_zero,Ext.biprodAddEquiv_apply_snd,Prod.snd_zero] using
           FiniteCoverCohomology.affine_open_ext_zero (X := X) W hW M 0
            ((Ext.mk₀ biprod.inr).comp z (zero_add _))
    simpa only [map_zero,Ext.biprodAddEquiv_apply_snd,Prod.snd_zero] using
      h ((Ext.mk₀ biprod.inr).comp middleClass (zero_add _))

end
end MaximalSeshadri.Geometry

end

end OAI
