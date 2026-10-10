import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeL2
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! Completion of the actual finite-mass sections on the prime cover.
The geometric Atkin pullback extends to a linear isometry of this space. -/
noncomputable section
open Topology
namespace CubicFirstMoment

local instance primeFiniteSections_addCommGroup {p : Eisenstein} (hp : primaryPrime p) :
    AddCommGroup (cubicThetaPrimeFiniteSections hp) := Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaPrimeAutomorphicL2 {p : Eisenstein} (hp : primaryPrime p) :
    Submodule ℂ (CubicThetaPrimeL2 hp) := (cubicThetaPrimeFiniteValue hp).range.topologicalClosure

instance cubicThetaPrimeAutomorphicL2_complete {p : Eisenstein} (hp : primaryPrime p) :
    CompleteSpace (cubicThetaPrimeAutomorphicL2 hp) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def cubicThetaPrimeFiniteEmbedding {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeFiniteSections hp →ₗ[ℂ] cubicThetaPrimeAutomorphicL2 hp :=
  (cubicThetaPrimeFiniteValue hp).codRestrict (cubicThetaPrimeAutomorphicL2 hp)
    (fun F => Submodule.le_topologicalClosure _ ⟨F,rfl⟩)

lemma cubicThetaPrimeFiniteEmbedding_dense {p : Eisenstein} (hp : primaryPrime p) :
    DenseRange (cubicThetaPrimeFiniteEmbedding hp) := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' Set.range (cubicThetaPrimeFiniteEmbedding hp)=
      Set.range (cubicThetaPrimeFiniteValue hp) := by
    ext y
    constructor
    · rintro ⟨v,⟨F,rfl⟩,rfl⟩
      exact ⟨F,rfl⟩
    · rintro ⟨F,rfl⟩
      exact ⟨cubicThetaPrimeFiniteEmbedding hp F,⟨F,rfl⟩,rfl⟩
  rw [he]
  exact u.property

def cubicThetaPrimeAtkinL2 {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeAutomorphicL2 hp →ₗᵢ[ℂ] cubicThetaPrimeAutomorphicL2 hp :=
  ((cubicThetaPrimeFiniteEmbedding hp).comp (cubicThetaPrimeFiniteAtkin hp)).extendOfIsometry
    (cubicThetaPrimeFiniteEmbedding_dense hp) (cubicThetaPrimeFiniteAtkin_norm hp)

lemma cubicThetaPrimeAtkinL2_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteSections hp) :
    cubicThetaPrimeAtkinL2 hp (cubicThetaPrimeFiniteEmbedding hp F)=
      cubicThetaPrimeFiniteEmbedding hp (cubicThetaPrimeFiniteAtkin hp F) :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
