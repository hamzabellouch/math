import OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars
import OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentInverseFinite

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveCoordinateFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] negativeCoordinateLaurentPresentation
  coordinateFramedTuple negativeCoordinateFrame LineBundle.inverse lineTensorInverseIso
variable {X Y : Scheme.{0}} {K σ : Type} [Field K] [Fintype σ]

theorem inversePower_cohomology_finite [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (L : LineBundle X) (s : σ → (structureSheaf X ⟶ L.sheaf)) (k : K →+* Γ(X,⊤))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)
    (n q : ℕ) :
    letI := Module.compHom (cohomology (L.pow n).inverse.sheaf q) k
    Module.Finite K (cohomology (L.pow n).inverse.sheaf q) := by
  let := LineBundleCoherent.lineBundle_isFinitePresentation (L.pow n).inverse
  let : (L.pow n).inverse.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (L.pow n).inverse.sheaf).choose.isQuasicoherent
  exact ActualLaurentExtFinite.cohomology_finite k
    (negativeCoordinateLaurentPresentation L.sheaf s k hc f hf n _
      (lineTensorInverseIso (L.pow n)))
    (negativeCoordinateLaurentPresentation_smul L.sheaf s k hc f hf n _
      (lineTensorInverseIso (L.pow n)))
    hc.ge
    (fun r t => IsAffineOpen.iInf
      (fun i => coordinateOpen_isAffine L.sheaf s k hc f hf (t i))) q

theorem coordinateBundle_cohomology_finite [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf X ⟶ L.sheaf))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade ℂ (Fin l)))
    (hf : sectionsMorphism (baseScalars p) s hc = f.hom)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  exact CoherentProjectiveFinite.coherent_cohomology_finite_of_inverse_powers
    p L l hl s hc (coordinateOpen_isAffine L.sheaf s (baseScalars p) hc f hf)
    (inversePower_cohomology_finite L s (baseScalars p) hc f hf) M q

theorem closed_coordinateBundle_cohomology_finite [IsNoetherian Y]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (i : X ⟶ Y) [IsClosedImmersion i]
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle Y) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf Y ⟶ L.sheaf))
    (hc : (⨆ j, PiExponentSeshadri.SectionOpens.isoOpen (s j)) = ⊤)
    (f : Y ≅ Proj (PolyGrade ℂ (Fin l)))
    (hf : sectionsMorphism (baseScalars p) s hc = f.hom)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars (i ≫ p))
    FiniteDimensional ℂ (cohomology M q) := by
  exact CoherentProjectiveFinite.closed_coherent_cohomology_finite_of_inverse_powers
    i p L l hl s hc (coordinateOpen_isAffine L.sheaf s (baseScalars p) hc f hf)
    (inversePower_cohomology_finite L s (baseScalars p) hc f hf) M q

end
end PiExponent.GeometrySupport.ProjectiveCoordinateFinite

end OAI
