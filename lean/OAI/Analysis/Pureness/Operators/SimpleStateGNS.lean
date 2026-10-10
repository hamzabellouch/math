import OAI.Analysis.Pureness.States.NormalizedPositiveState
import OAI.Analysis.Pureness.Operators.SimpleCStarAlgebraic
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder InnerProductSpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def stateGNSVector (f : A →ₚ[ℂ] ℂ) : f.GNS := f.toPreGNS 1

lemma stateGNSVector_norm (f : A →ₚ[ℂ] ℂ) (h1 : f 1 = 1) :
    ‖stateGNSVector f‖ = 1 := by
  have h := f.preGNS_norm_sq (f.toPreGNS 1)
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, h1] at h
  have h' : ‖f.toPreGNS 1‖ ^ 2 = 1 := by exact_mod_cast h
  simpa [stateGNSVector] using (sq_eq_one_iff.mp h').resolve_right
    (by have := norm_nonneg (f.toPreGNS 1); linarith)

lemma stateGNS_apply_vector (f : A →ₚ[ℂ] ℂ) (a : A) :
    f.gnsStarAlgHom a (stateGNSVector f) = (f.toPreGNS a : f.GNS) := by
  simp [stateGNSVector, PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.leftMulMapPreGNS]

lemma stateGNS_vector_value (f : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪stateGNSVector f, f.gnsStarAlgHom a (stateGNSVector f)⟫_ℂ = f a := by
  rw [stateGNS_apply_vector]
  simp [stateGNSVector, UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]

lemma stateGNS_cyclic (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a => f.gnsStarAlgHom a (stateGNSVector f)) := by
  simp only [stateGNS_apply_vector]
  exact UniformSpace.Completion.denseRange_coe.comp f.toPreGNS.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

lemma stateGNS_nontrivial (f : A →ₚ[ℂ] ℂ) (h1 : f 1 = 1) : Nontrivial f.GNS := by
  refine ⟨⟨stateGNSVector f, 0, ?_⟩⟩
  intro h
  have := stateGNSVector_norm f h1
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem simple_stateGNS_injective [Nontrivial A] (hsimple : TopologicallySimple A)
    (f : A →ₚ[ℂ] ℂ) (h1 : f 1 = 1) : Function.Injective f.gnsStarAlgHom := by
  let := stateGNS_nontrivial f h1
  let := topologicallySimple_isSimpleRing hsimple
  exact f.gnsStarAlgHom.toRingHom.injective

variable (A) [Nontrivial A]

def chosenPositiveState : A →ₚ[ℂ] ℂ := Classical.choose (exists_normalizedPositiveState (A := A))

lemma chosenPositiveState_one : chosenPositiveState A 1 = 1 :=
  Classical.choose_spec (exists_normalizedPositiveState (A := A))

abbrev SimpleStateHilbert := (chosenPositiveState A).GNS

instance simpleStateHilbert_nontrivial : Nontrivial (SimpleStateHilbert A) :=
  stateGNS_nontrivial _ (chosenPositiveState_one A)

def simpleStateGNS : A →⋆ₐ[ℂ] (SimpleStateHilbert A →L[ℂ] SimpleStateHilbert A) :=
  (chosenPositiveState A).gnsStarAlgHom

theorem simpleStateGNS_injective (hsimple : TopologicallySimple A) :
    Function.Injective (simpleStateGNS A) :=
  simple_stateGNS_injective hsimple _ (chosenPositiveState_one A)

theorem simpleStateGNS_isometry (hsimple : TopologicallySimple A) :
    Isometry (simpleStateGNS A) :=
  NonUnitalStarAlgHom.isometry (simpleStateGNS A).toNonUnitalStarAlgHom
    (simpleStateGNS_injective A hsimple)

theorem simpleStateGNS_norm (hsimple : TopologicallySimple A) (a : A) :
    ‖simpleStateGNS A a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (simpleStateGNS A).toNonUnitalStarAlgHom
    (simpleStateGNS_injective A hsimple) a
end CuntzPureness

end

end OAI
