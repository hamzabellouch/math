import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootL2
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! Completion of the actual finite-mass sections on the root cover.
Its fractional translations extend isometrically to this space. -/
noncomputable section
open Topology
namespace CubicFirstMoment

local instance cubeRootFiniteSections_addCommGroup {p : Eisenstein} (hp : primaryPrime p) :
    AddCommGroup (cubicThetaPrimeCubeRootFiniteSections hp) := Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaPrimeCubeRootAutomorphicL2 {p : Eisenstein} (hp : primaryPrime p) :
    Submodule ℂ (CubicThetaPrimeCubeRootL2 hp) := (cubicThetaPrimeCubeRootFiniteValue hp).range.topologicalClosure

instance cubicThetaPrimeCubeRootAutomorphicL2_complete {p : Eisenstein} (hp : primaryPrime p) :
    CompleteSpace (cubicThetaPrimeCubeRootAutomorphicL2 hp) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def cubicThetaPrimeCubeRootFiniteEmbedding {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootFiniteSections hp →ₗ[ℂ] cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  (cubicThetaPrimeCubeRootFiniteValue hp).codRestrict (cubicThetaPrimeCubeRootAutomorphicL2 hp)
    (fun F => Submodule.le_topologicalClosure _ ⟨F,rfl⟩)

lemma cubicThetaPrimeCubeRootFiniteEmbedding_dense {p : Eisenstein} (hp : primaryPrime p) :
    DenseRange (cubicThetaPrimeCubeRootFiniteEmbedding hp) := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' Set.range (cubicThetaPrimeCubeRootFiniteEmbedding hp)=
      Set.range (cubicThetaPrimeCubeRootFiniteValue hp) := by
    ext y
    constructor
    · rintro ⟨v,⟨F,rfl⟩,rfl⟩
      exact ⟨F,rfl⟩
    · rintro ⟨F,rfl⟩
      exact ⟨cubicThetaPrimeCubeRootFiniteEmbedding hp F,⟨F,rfl⟩,rfl⟩
  rw [he]
  exact u.property

def cubicThetaPrimeCubeRootTranslateL2 {p : Eisenstein} (hp : primaryPrime p) (x : Eisenstein) :
    cubicThetaPrimeCubeRootAutomorphicL2 hp →ₗᵢ[ℂ] cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  ((cubicThetaPrimeCubeRootFiniteEmbedding hp).comp (cubicThetaPrimeCubeRootFiniteTranslate hp x)).extendOfIsometry
    (cubicThetaPrimeCubeRootFiniteEmbedding_dense hp) (cubicThetaPrimeCubeRootFiniteTranslate_norm hp x)

lemma cubicThetaPrimeCubeRootTranslateL2_finite {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootTranslateL2 hp x (cubicThetaPrimeCubeRootFiniteEmbedding hp F)=
      cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootFiniteTranslate hp x F) :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
