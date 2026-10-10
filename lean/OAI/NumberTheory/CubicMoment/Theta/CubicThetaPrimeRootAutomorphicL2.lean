import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootL2
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! Completion of the actual finite-mass sections on the root cover.
The geometric Weyl pullback extends to a linear isometry of this space. -/
noncomputable section
open Topology
namespace CubicFirstMoment

local instance rootFiniteSections_addCommGroup {p : Eisenstein} (hp : primaryPrime p) :
    AddCommGroup (cubicThetaPrimeRootFiniteSections hp) := Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaPrimeRootAutomorphicL2 {p : Eisenstein} (hp : primaryPrime p) :
    Submodule ℂ (CubicThetaPrimeRootL2 hp) := (cubicThetaPrimeRootFiniteValue hp).range.topologicalClosure

instance cubicThetaPrimeRootAutomorphicL2_complete {p : Eisenstein} (hp : primaryPrime p) :
    CompleteSpace (cubicThetaPrimeRootAutomorphicL2 hp) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def cubicThetaPrimeRootFiniteEmbedding {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootFiniteSections hp →ₗ[ℂ] cubicThetaPrimeRootAutomorphicL2 hp :=
  (cubicThetaPrimeRootFiniteValue hp).codRestrict (cubicThetaPrimeRootAutomorphicL2 hp)
    (fun F => Submodule.le_topologicalClosure _ ⟨F,rfl⟩)

lemma cubicThetaPrimeRootFiniteEmbedding_dense {p : Eisenstein} (hp : primaryPrime p) :
    DenseRange (cubicThetaPrimeRootFiniteEmbedding hp) := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' Set.range (cubicThetaPrimeRootFiniteEmbedding hp)=
      Set.range (cubicThetaPrimeRootFiniteValue hp) := by
    ext y
    constructor
    · rintro ⟨v,⟨F,rfl⟩,rfl⟩
      exact ⟨F,rfl⟩
    · rintro ⟨F,rfl⟩
      exact ⟨cubicThetaPrimeRootFiniteEmbedding hp F,⟨F,rfl⟩,rfl⟩
  rw [he]
  exact u.property

def cubicThetaPrimeRootWeylL2 {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootAutomorphicL2 hp →ₗᵢ[ℂ] cubicThetaPrimeRootAutomorphicL2 hp :=
  ((cubicThetaPrimeRootFiniteEmbedding hp).comp (cubicThetaPrimeRootFiniteWeyl hp)).extendOfIsometry
    (cubicThetaPrimeRootFiniteEmbedding_dense hp) (cubicThetaPrimeRootFiniteWeyl_norm hp)

lemma cubicThetaPrimeRootWeylL2_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootFiniteSections hp) :
    cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootFiniteEmbedding hp F)=
      cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootFiniteWeyl hp F) :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
