import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateScalars
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeCoordinates

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque
open PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] coordinateFramedTuple negativeCoordinateFrame
private abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
variable (n : ℕ) (N : X.Modules) (E : moduleTensor X (modulePow X M n) N ≅ O X)
local instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen_1
    (U : X.Opens) (P : X.Modules) :
    Module Γ(X,⊤) (schemeFreeOpen X U ⟶ P) := sheafHomModule X _ P

lemma negativeCoordinateLaurentPresentation_smul (q : ℕ) (t : Fin (q + 1) → σ)
    (c : K) (b : schemeFreeOpen X
      (PiExponent.GeometrySupport.CechHigher.intersection (fun i => SectionOpens.isoOpen (s i)) t) ⟶ N) :
    (negativeCoordinateLaurentPresentation M s k hc f hf n N E).coefficient q t ((k c) • b) =
      c • (negativeCoordinateLaurentPresentation M s k hc f hf n N E).coefficient q t b :=
  coordinateFramedTuple_smul M s k hc f hf N (fun i => negativeCoordinateFrame n E (s i))
    (-(n : ℤ)) q t c b

lemma coordinateInversePowerLaurentPresentation_smul (q : ℕ) (t : Fin (q + 1) → σ)
    (c : K) (b : schemeFreeOpen X
      (PiExponent.GeometrySupport.CechHigher.intersection (fun i => SectionOpens.isoOpen (s i)) t) ⟶
        ((coordinateLineBundle M s hc).pow n).inverse.sheaf) :
    (coordinateInversePowerLaurentPresentation M s k hc f hf n).coefficient q t ((k c) • b) =
      c • (coordinateInversePowerLaurentPresentation M s k hc f hf n).coefficient q t b :=
  negativeCoordinateLaurentPresentation_smul M s k hc f hf n _
    (lineTensorInverseIso ((coordinateLineBundle M s hc).pow n)) q t c b

lemma coordinateLaurentCechPresentation_smul (q : ℕ) (t : Fin (q + 1) → σ)
    (c : K) (b : schemeFreeOpen X
      (PiExponent.GeometrySupport.CechHigher.intersection (fun i => SectionOpens.isoOpen (s i)) t) ⟶
        modulePow X M n) :
    (coordinateLaurentCechPresentation M s k hc f hf n).coefficient q t ((k c) • b) =
      c • (coordinateLaurentCechPresentation M s k hc f hf n).coefficient q t b := by
  have h :
      coordinateFramedTuple M s k hc f hf (modulePow X M n)
        (fun i => coordinatePowerFrame (s i) n) n q t ((k c) • b) =
      c • coordinateFramedTuple M s k hc f hf (modulePow X M n)
        (fun i => coordinatePowerFrame (s i) n) n q t b := by
    simpa only using! coordinateFramedTuple_smul M s k hc f hf (modulePow X M n)
      (fun i => coordinatePowerFrame (s i) n) n q t c b
  erw [coordinateFramedTuple, coordinateFramedOverlap] at h
  simpa only [coordinateLaurentCechPresentation,
    PiExponent.GeometrySupport.ProjectiveTupleCharts.coordinateTupleCoefficient,
    coordinatePowerOverlap] using! h

end
end PiExponentSeshadri.Projective

end OAI
