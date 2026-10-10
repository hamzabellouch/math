import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Identity
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceBasics

namespace OAI

namespace PiExponent.ProjectiveO1
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PiExponentSeshadri.Geometry

attribute [local irreducible] lineBundle coordinateSection scalars

private abbrev schemeUnit (X : Scheme.{0}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

variable (R σ : Type) [CommRing R] [IsNoetherianRing R] [Fintype σ]

theorem standardPower_ext_eq_zero (n q : ℕ) (hq : 0 < q)
    (x : Ext.{1} (C := (projectiveSpace R σ).Modules) (schemeUnit (projectiveSpace R σ))
      (modulePow (projectiveSpace R σ) (lineBundle (R := R) (σ := σ)).sheaf n) q) :
    x = 0 := by
  exact PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity.coordinatePower_ext_eq_zero
    (X := projectiveSpace R σ) (K := R) (σ := σ)
    (lineBundle (R := R) (σ := σ)).sheaf
    (coordinateSection (R := R) (σ := σ)) (scalars (R := R) (σ := σ))
    (coordinateSection_cover (R := R) (σ := σ)) (Iso.refl (projectiveSpace R σ))
    (coordinate_sectionsMorphism_identity (R := R) (σ := σ)) n q hq x

theorem serre_vanishing [Nonempty σ]
    (M : (projectiveSpace R σ).Modules) [M.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (C := (projectiveSpace R σ).Modules) (schemeUnit (projectiveSpace R σ))
        ((moduleTwistFunctor (lineBundle (R := R) (σ := σ)) n).obj M) q, x = 0 := by
  let e := Fintype.equivFin σ
  let s : Fin (Fintype.card σ) →
      (structureSheaf (projectiveSpace R σ) ⟶ (lineBundle (R := R) (σ := σ)).sheaf) :=
    fun i => coordinateSection (e.symm i)
  have hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤ := by
    change (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen
      (coordinateSection (R := R) (e.symm i))) = ⊤
    exact (Equiv.iSup_comp
      (g := fun j : σ => PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) j))
      e.symm).trans (coordinateSection_cover (R := R) (σ := σ))
  apply PiExponent.GeometrySupport.SerreAssembly.eventual_twist_ext_zero_of_section_cover
    (lineBundle (R := R) (σ := σ)) (Fintype.card σ) Fintype.card_pos s hcover
    (fun i => coordinateSection_isAffineOpen (e.symm i)) _ M
  intro n q hq x
  exact standardPower_ext_eq_zero R σ n q hq x

end
end PiExponent.ProjectiveO1

end OAI
