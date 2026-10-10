import OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws
import OAI.NumberTheory.PiExponent.Approximation.TwistPresentations
import OAI.NumberTheory.PiExponent.Cohomology.CohomologyIso
import OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentExtFiniteness

namespace OAI

namespace PiExponent.NegativeTwistPresentations
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport.TwistPresentations
variable {X : Scheme.{0}}

def cancelIso (M : X.Modules) (L N : LineBundle X)
    (e : moduleTensor X L.sheaf N.sheaf ≅ structureSheaf X) :
    moduleTensor X (moduleTensor X M L.sheaf) N.sheaf ≅ M :=
  moduleLineTensorAssoc M L N ≪≫ moduleTensorIso (Iso.refl M) e ≪≫ moduleTensorRightUnit M

variable (L N : LineBundle X) {M : X.Modules} {n : ℕ}
    (s : ((moduleTwistFunctor L n).obj M).GeneratingSections)
    (e : moduleTensor X (L.pow n).sheaf N.sheaf ≅ structureSheaf X)

def presentationMap : moduleTensor X (SheafOfModules.free s.I) N.sheaf ⟶ M :=
  moduleTensorMap (s.π ≫ (moduleTwistPowerIso L M n).hom) (𝟙 N.sheaf) ≫
    (cancelIso M (L.pow n) N e).hom

instance presentationMap_epi : Epi (presentationMap L N s e) := by
  let g : (SheafOfModules.free s.I : X.Modules) ⟶ moduleTensor X M (L.pow n).sheaf :=
    s.π ≫ (moduleTwistPowerIso L M n).hom
  let : Epi (C := X.Modules) s.π := s.epi
  let hg : Epi (C := X.Modules) g := epi_comp (C := X.Modules) s.π (moduleTwistPowerIso L M n).hom
  let : Epi (C := X.Modules) (moduleTensorMap g (𝟙 N.sheaf)) :=
    @moduleTensorMap_epi X _ _ g hg N
  exact epi_comp (C := X.Modules) (moduleTensorMap g (𝟙 N.sheaf))
    (cancelIso M (L.pow n) N e).hom

def middleIsoBiproduct [Fintype s.I] [HasFiniteBiproducts X.Modules] :
    moduleTensor X (SheafOfModules.free s.I) N.sheaf ≅ ⨁ (fun _ : s.I => N.sheaf) :=
  twistFreeIsoBiproduct N 1 s.I ≪≫
    biproduct.mapIso (fun _ : s.I => moduleTensorRightUnit N.sheaf)

theorem middle_isFinitePresentation [hs : s.IsFiniteType] :
    (moduleTensor X (SheafOfModules.free s.I) N.sheaf).IsFinitePresentation := by
  let : Finite s.I := hs.finite
  have := PiExponent.FiniteGlobalPresentation.free_isFinitePresentation X s.I
  exact PiExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation N 1
    (SheafOfModules.free s.I)

theorem kernel_isFinitePresentation [IsLocallyNoetherian X] [M.IsFinitePresentation]
    [s.IsFiniteType] : (kernel (presentationMap L N s e)).IsFinitePresentation := by
  have := middle_isFinitePresentation L N s
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  exact PiExponent.FiniteGlobalPresentation.kernel_isFinitePresentation (presentationMap L N s e)

theorem presentation_shortExact :
    (ShortComplex.mk (kernel.ι (presentationMap L N s e)) (presentationMap L N s e)
      (kernel.condition (presentationMap L N s e))).ShortExact :=
  { exact := ShortComplex.exact_kernel (presentationMap L N s e) }

theorem middle_cohomology_finite (p : X ⟶ Spec (CommRingCat.of ℂ)) [hs : s.IsFiniteType]
    (q : ℕ)
    (hN : letI := Module.compHom (cohomology N.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf q)) :
    letI := Module.compHom
      (cohomology (moduleTensor X (SheafOfModules.free s.I) N.sheaf) q) (baseScalars p)
    FiniteDimensional ℂ (cohomology (moduleTensor X (SheafOfModules.free s.I) N.sheaf) q) := by
  let : Finite s.I := hs.finite
  let : Fintype s.I := Fintype.ofFinite s.I
  let : HasFiniteBiproducts X.Modules := Abelian.hasFiniteBiproducts
  let B := ⨁ (fun _ : s.I => N.sheaf)
  let := Module.compHom (cohomology B q) (baseScalars p)
  let := Module.compHom
    (cohomology (moduleTensor X (SheafOfModules.free s.I) N.sheaf) q) (baseScalars p)
  have : FiniteDimensional ℂ (cohomology B q) :=
    CoherentExtFiniteness.cohomology_finite_of_biproduct p
      (biproduct.isBilimit (fun _ : s.I => N.sheaf)) q (fun _ => hN)
  exact Module.Finite.of_surjective (cohomologyIso p (middleIsoBiproduct L N s) q).symm.toLinearMap
    (cohomologyIso p (middleIsoBiproduct L N s) q).symm.surjective

def coherentFinitePresentation [IsLocallyNoetherian X] [M.IsFinitePresentation]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [s.IsFiniteType]
    (hN : ∀ q, letI := Module.compHom (cohomology N.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf q)) :
    CoherentExtFiniteness.CoherentFinitePresentation p M where
  kernel := kernel (presentationMap L N s e)
  kernel_coherent := kernel_isFinitePresentation L N s e
  middle := moduleTensor X (SheafOfModules.free s.I) N.sheaf
  left := kernel.ι (presentationMap L N s e)
  right := presentationMap L N s e
  comp_zero := kernel.condition (presentationMap L N s e)
  shortExact := presentation_shortExact L N s e
  middle_finite := fun q => middle_cohomology_finite L N s p q (hN q)

end
end PiExponent.NegativeTwistPresentations

end OAI
