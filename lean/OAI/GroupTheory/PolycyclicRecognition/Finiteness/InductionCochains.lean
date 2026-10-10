import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalInductionExact
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

namespace OAI

/-! # Frobenius reciprocity for the induced resolution's cochains -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def normalInductionCochainsIso (P : ProjectiveResolution (Rep.trivial ℤ N ℤ))
    (A : Rep ℤ G) :
    (normalInducedResolution ℤ N P).complex.linearYonedaObj ℤ A ≅
      P.complex.linearYonedaObj ℤ (Rep.res N.subtype A) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (Rep.indResHomEquiv N.subtype (P.complex.X i) A).toModuleIso) (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change P.complex.d j i ≫ Rep.indResHomEquiv N.subtype (P.complex.X i) A f =
        Rep.indResHomEquiv N.subtype (P.complex.X j) A (Rep.indMap N.subtype (P.complex.d j i) ≫ f)
      exact ((Rep.indResAdjunction ℤ N.subtype).homEquiv_naturality_left (P.complex.d j i) f).symm)

def normalInducedCohomologyIso
    (P : ProjectiveResolution (Rep.trivial ℤ N ℤ)) (A : Rep ℤ G) (i : ℕ) :
    groupCohomology (Rep.res N.subtype A) i ≅
      ((normalInducedResolution ℤ N P).complex.linearYonedaObj ℤ A).homology i :=
  groupCohomologyIso (Rep.res N.subtype A) i P ≪≫
    (HomologicalComplex.homologyFunctor _ _ i).mapIso
      (normalInductionCochainsIso N P A).symm

end PolycyclicRecognition

end

end OAI
