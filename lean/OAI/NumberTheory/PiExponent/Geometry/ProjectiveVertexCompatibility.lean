import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteValues
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveTupleCharts

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)

lemma coordinatePowerOverlap_restrictVertex (n : ℕ) (i : σ)
    (a : Finset (ChartVariables i))
    (b : freeOpen X.ringCatSheaf (SectionOpens.isoOpen (s i)) ⟶ modulePow X M n) :
    coordinatePowerOverlap M s k hc f hf n i a
      (freeOpenMap X.ringCatSheaf (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)) ≫ b) =
      coordinatePowerVertex M k s hc f hf n i b := by
  change overlapLaurent i (n : ℤ) a
    (coordinateFiniteRingEquiv M s k hc f hf i a
      (framedHomCoefficientsEquiv _ (modulePow X M n)
        (restrictOpenFrame inf_le_left (coordinatePowerFrame (s i) n))
        (freeOpenMap X.ringCatSheaf (homOfLE _) ≫ b))) =
    vertexLaurent i (n : ℤ) (coordinateSectionRingEquiv M k s hc f hf i
      (framedHomCoefficientsEquiv _ (modulePow X M n) (coordinatePowerFrame (s i) n) b))
  erw [framedHomCoefficientsEquiv_restrict]
  erw [coordinateFiniteRingEquiv_restrict_apply M s k hc f hf i a]
  exact overlapLaurent_base i (n : ℤ) a _

lemma coordinateTupleCoefficient_restrictVertex (n q : ℕ) (t : Fin (q+1) → σ)
    (b : freeOpen X.ringCatSheaf (SectionOpens.isoOpen (s (t 0))) ⟶ modulePow X M n) :
    coordinateTupleCoefficient M s k hc f hf n q t
      (freeOpenMap X.ringCatSheaf (homOfLE
        (iInf_le (fun j => SectionOpens.isoOpen (s (t j))) 0)) ≫ b) =
      coordinatePowerVertex M k s hc f hf n (t 0) b := by
  change coordinatePowerOverlap M s k hc f hf n (t 0) (tupleVariables t 0)
    (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)
      (freeOpenMap X.ringCatSheaf (homOfLE _) ≫ b)) = _
  have h : freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)
      (freeOpenMap X.ringCatSheaf (homOfLE
        (iInf_le (fun j => SectionOpens.isoOpen (s (t j))) 0)) ≫ b) =
      freeOpenMap X.ringCatSheaf (homOfLE (show coordinateFiniteOpen M s (t 0)
        (tupleVariables t 0) ≤ SectionOpens.isoOpen (s (t 0)) from inf_le_left)) ≫ b := by
    change freeOpenMap X.ringCatSheaf _ ≫ (freeOpenMap X.ringCatSheaf _ ≫ b) = _
    simp only [freeOpenMap]
    erw [← Functor.map_comp_assoc, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  rw [h]
  exact coordinatePowerOverlap_restrictVertex M s k hc f hf n (t 0) (tupleVariables t 0) b

end
end PiExponentSeshadri.Projective

end OAI
