import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Definitions
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SurfaceH0Finite
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionCoefficientOrder
import OAI.AlgebraicGeometry.Seshadri.Lattice.NodePolygon
import OAI.AlgebraicGeometry.Seshadri.Interpolation.ActualInterpolation

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.ActualInterpolation MaximalSeshadri.LocalComparison

variable {X : Scheme.{0}}

lemma global_smul_eq_scalarEnd {M : X.Modules} (r : Γ(X,⊤)) (s : O X ⟶ M) :
    r • s = scalarEnd r ≫ s := by
  ext U a
  change Γ(X,U) at a
  change (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) • s.app U a =
    s.app U ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) * a)
  exact (s.app_smul _ _).symm

def affineCoefficientLinear (g : X ⟶ Spec (CommRingCat.of ℂ))
    {M : X.Modules} (U : X.affineOpens) (e : M.restrict U.1.ι ≅ O U.1.toScheme) :
    letI := complexSectionModule g M
    letI : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra
    GlobalSections X M →ₗ[ℂ] Γ(X,U.1) := by
  letI := complexSectionModule g M
  letI : Algebra ℂ Γ(X,U.1) := (openScalars g U.1).toAlgebra
  refine { toFun := affineCoefficient U e
           map_add' := ?_
           map_smul' := ?_ }
  · intro s t
    exact (congrArg (fun sectionValue => U.1.topIso.hom (coefficient e sectionValue))
      (restrictSection_add U.1.ι s t)).trans
      ((congrArg U.1.topIso.hom
        (coefficient_add e (restrictSection U.1.ι s) (restrictSection U.1.ι t))).trans
        (map_add U.1.topIso.hom.hom _ _))
  · intro c s
    change affineCoefficient U e (baseScalars g c • s) =
      openScalars g U.1 c * affineCoefficient U e s
    refine (congrArg (affineCoefficient U e)
      (global_smul_eq_scalarEnd (baseScalars g c) s)).trans ?_
    refine (congrArg U.1.topIso.hom
      (coefficient_restrict_scalar_comp U.1.ι e (baseScalars g c) s)).trans ?_
    refine (map_mul U.1.topIso.hom.hom _ _).trans ?_
    apply congrArg (fun value => value * affineCoefficient U e s)
    change (U.1.ι.appTop ≫ U.1.topIso.hom) (baseScalars g c) = openScalars g U.1 c
    have H := congrArg (fun f : ℂ →+* Γ(X,U.1) => f c) (topIso_baseScalars g U.1)
    rw [baseScalars_comp_actual] at H
    exact H

lemma affineCoefficientLinear_injective [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Function.Injective (affineCoefficientLinear g U e) := by
  intro s t h
  apply L.restricted_coefficient_injective U.1.ι e
  exact (ConcreteCategory.bijective_of_isIso U.1.topIso.hom).injective h

lemma Surface.sections_finite (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
    (M : LineBundle S.scheme) :
    letI := complexSectionModule S.structureMap M.sheaf
    Module.Finite ℂ (GlobalSections S.scheme M.sheaf) := by
  let := complexSectionModule S.structureMap M.sheaf
  let := Module.compHom (cohomology M.sheaf 0) (baseScalars S.structureMap)
  let := S.H0_finite L hL M
  let e := Ext.linearEquiv₀ (R := Γ(S.scheme,⊤)) (X := structureSheaf S.scheme) (Y := M.sheaf)
  exact Module.Finite.equiv (show cohomology M.sheaf 0 ≃ₗ[ℂ] GlobalSections S.scheme M.sheaf from
    { e.toAddEquiv with map_smul' := fun r x => e.map_smul (baseScalars S.structureMap r) x })

lemma germCoefficients_eq_bivariate {A M : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup M] [Module ℂ M] (coord : M →ₗ[ℂ] A)
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ)) (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0) (s : M) :
    germCoefficients coord q hq s = NodalLocal.bivariateCoeff (bivariateTaylor q hq (coord s)) := by
  funext e
  exact (biCoeff_biSeries _ e).symm

lemma germCoefficients_injective_of_taylor {A M : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup M] [Module ℂ M] (coord : M →ₗ[ℂ] A)
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ)) (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (hc : Function.Injective coord) (ht : Function.Injective (analyticTaylor q hq)) :
    Function.Injective (germCoefficients coord q hq) := by
  intro s t h
  apply hc
  apply ht
  exact congrArg (fun c => (FormalCoordinates.binaryEquiv ℂ).symm (biSeries c)) h
end
end MaximalSeshadri.Geometry

end

end OAI
