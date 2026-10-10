import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech
import OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeFrames
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeTransitions

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
variable (n : ℕ) (N : X.Modules) (E : moduleTensor X (modulePow X M n) N ≅ O X)

lemma negativeCoordinateOverlap_restrict (i j : σ)
    (a : Finset (ChartVariables i)) (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
    (z : freeOpen X.ringCatSheaf (coordinateFiniteOpen M s i a) ⟶ N) :
    coordinateFramedOverlap M s k hc f hf N (fun i => negativeCoordinateFrame n E (s i))
      (-(n : ℤ)) j b (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z) =
    coordinateFramedOverlap M s k hc f hf N (fun i => negativeCoordinateFrame n E (s i))
      (-(n : ℤ)) i a z := by
  let ci := framedHomCoefficientsEquiv (coordinateFiniteOpen M s i a) N
    (restrictOpenFrame inf_le_left (negativeCoordinateFrame n E (s i))) z
  let ri := coordinateFiniteRingEquiv M s k hc f hf i a
  let rj := coordinateFiniteRingEquiv M s k hc f hf j b
  let u := coordinateRatioOn (s i) (s j) (h.trans inf_le_left)
  have ht : coordinateFiniteTransition M s k hc f hf i j a b h (ri ci) =
      rj (X.presheaf.map (homOfLE h).op ci) := by
    simp only [coordinateFiniteTransition, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ri, RingEquiv.symm_apply_apply, rj]
  dsimp only [coordinateFramedOverlap, framedLaurentOverlap, framedHomRingEquiv]
  dsimp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.trans_apply, RingEquiv.coe_toAddEquiv]
  change overlapLaurent j (-(n : ℤ)) b
    (rj (framedHomCoefficientsEquiv (coordinateFiniteOpen M s j b) N
      (restrictOpenFrame inf_le_left (negativeCoordinateFrame n E (s j)))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z))) =
    overlapLaurent i (-(n : ℤ)) a (ri ci)
  have hcoef : framedHomCoefficientsEquiv (coordinateFiniteOpen M s j b) N
      (restrictOpenFrame inf_le_left (negativeCoordinateFrame n E (s j)))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z) =
      u ^ n * X.presheaf.map (homOfLE h).op ci :=
    negativeCoordinateFrame_hom_change_restrict n E (s i) (s j)
      (U := coordinateFiniteOpen M s i a) (W := coordinateFiniteOpen M s j b)
      inf_le_left inf_le_left h z
  rw [hcoef, map_mul, map_pow]
  change overlapLaurent j (-(n : ℤ)) b
    ((rj u) ^ n * rj (X.presheaf.map (homOfLE h).op ci)) = _
  rw [← ht]
  exact coordinateNegativeLaurent_change M s k hc f hf n i j a b h (ri ci)

def negativeCoordinateLaurentPresentation :
    PiExponent.ProjectiveTwistCech.LaurentCechPresentation (K := K)
      (fun i => SectionOpens.isoOpen (s i)) N (-(n : ℤ)) :=
  coordinateFramedLaurentPresentation M s k hc f hf N
    (fun i => negativeCoordinateFrame n E (s i)) (-(n : ℤ))
    (negativeCoordinateOverlap_restrict M s k hc f hf n N E)

def coordinateInversePowerLaurentPresentation :
    PiExponent.ProjectiveTwistCech.LaurentCechPresentation (K := K)
      (fun i => SectionOpens.isoOpen (s i))
      (((coordinateLineBundle M s hc).pow n).inverse.sheaf) (-(n : ℤ)) :=
  negativeCoordinateLaurentPresentation M s k hc f hf n _
    (lineTensorInverseIso ((coordinateLineBundle M s hc).pow n))

end
end PiExponentSeshadri.Projective

end OAI
