import OAI.Analysis.Cotype.PairedExtension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.BigOperators.Pi

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {𝕜 : Type*} [Field 𝕜]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def coordinateDual : (ι → 𝕜) ≃ₗ[𝕜] Module.Dual 𝕜 (ι → 𝕜) where
  toFun v :=
    { toFun := fun w => ∑ i, v i * w i
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intro t x; simp [Finset.mul_sum, mul_left_comm] }
  invFun f i := f (Pi.single i 1)
  left_inv := by intro v; funext i; simp [Pi.single_apply]
  right_inv := by
    intro f
    apply LinearMap.ext
    intro x
    change (∑ i, f (Pi.single i 1) * x i) = f x
    conv_rhs => rw [pi_eq_sum_univ' x, map_sum]
    simp [mul_comm]
  map_add' := by intro x y; ext w; simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by intro t x; ext w; simp [mul_assoc, Finset.mul_sum]

@[simp] theorem coordinateDual_apply (v w : ι → 𝕜) :
    coordinateDual v w = ∑ i, v i * w i := rfl

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

theorem frame_evaluation_surjective (V : κ → Module.Dual 𝕜 E)
    (hV : LinearIndependent 𝕜 V) : Function.Surjective (LinearMap.pi V) := by
  apply LinearMap.dualMap_injective_iff.mp
  intro φ ψ h
  obtain ⟨c,rfl⟩ := coordinateDual.surjective φ
  obtain ⟨d,rfl⟩ := coordinateDual.surjective ψ
  congr 1
  apply hV.fintypeLinearCombination_injective
  have he (a : κ → 𝕜) :
      (LinearMap.pi V).dualMap (coordinateDual a) = Fintype.linearCombination 𝕜 V a := by
    ext x
    simp [coordinateDual_apply, Fintype.linearCombination_apply]
  rwa [he, he] at h

theorem paired_frames_orbit [FiniteDimensional 𝕜 E]
    (U U' : ι → E) (V V' : κ → Module.Dual 𝕜 E)
    (hU : LinearIndependent 𝕜 U) (hU' : LinearIndependent 𝕜 U')
    (hV : LinearIndependent 𝕜 V) (hV' : LinearIndependent 𝕜 V')
    (hpair : ∀ i j, V j (U i) = V' j (U' i)) :
    ∃ H : E ≃ₗ[𝕜] E, (∀ i, H (U i) = U' i) ∧ ∀ j x, V' j (H x) = V j x := by
  let f := Fintype.linearCombination 𝕜 U
  let f' := Fintype.linearCombination 𝕜 U'
  have hp : (LinearMap.pi V).comp f = (LinearMap.pi V').comp f' := by
    ext c j
    simp [f, f', Fintype.linearCombination_apply, hpair]
  obtain ⟨H,hH,hpH⟩ := exists_paired_extension f f' (LinearMap.pi V) (LinearMap.pi V')
    hU.fintypeLinearCombination_injective hU'.fintypeLinearCombination_injective
    (frame_evaluation_surjective V hV) (frame_evaluation_surjective V' hV') hp
  refine ⟨H, ?_, fun j x => congrFun (hpH x) j⟩
  intro i
  simpa [f, f', Fintype.linearCombination_apply] using hH (Pi.single i 1)

end Cotype

end

end OAI
