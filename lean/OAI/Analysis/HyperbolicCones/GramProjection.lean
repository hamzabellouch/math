import OAI.Analysis.HyperbolicCones.Model

namespace OAI

noncomputable section

open scoped ContDiff
open ContinuousLinearMap

universe u v w

namespace Paper256

section Gram

variable {E : Type u} {F : Type v} {W : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace E] [CompleteSpace F]

def gramProjection (T : E →L[ℝ] F) : F →L[ℝ] F :=
  T.comp ((Ring.inverse (T.adjoint.comp T)).comp T.adjoint)

theorem gram_isUnit_of_injective [FiniteDimensional ℝ E]
    (T : E →L[ℝ] F) (hT : Function.Injective T) : IsUnit (T.adjoint.comp T) := by
  have hk : (T.adjoint.comp T).ker = ⊥ := by
    rw [T.ker_adjoint_comp_self]
    exact LinearMap.ker_eq_bot.mpr hT
  have hi : Function.Injective (T.adjoint.comp T) := LinearMap.ker_eq_bot.mp hk
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi, LinearMap.surjective_of_injective hi⟩

theorem gramProjection_eq [FiniteDimensional ℝ F]
    (T : E →L[ℝ] F) (hT : IsUnit (T.adjoint.comp T)) :
    gramProjection T = T.range.starProjection := by
  ext y
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨Ring.inverse (T.adjoint.comp T) (T.adjoint y), rfl⟩
  · rw [T.orthogonal_range]
    change T.adjoint (y - T (Ring.inverse (T.adjoint.comp T) (T.adjoint y))) = 0
    rw [map_sub]
    change T.adjoint y - ((T.adjoint.comp T) * Ring.inverse (T.adjoint.comp T))
      (T.adjoint y) = 0
    rw [Ring.mul_inverse_cancel _ hT]
    simp

theorem one_sub_gramProjection_eq_kernel [FiniteDimensional ℝ F]
    (T : E →L[ℝ] F) (hT : IsUnit (T.adjoint.comp T))
    (A : F →L[ℝ] F) (hA : IsSelfAdjoint A) (hr : T.range = A.range) :
    1 - gramProjection T = A.ker.starProjection := by
  rw [gramProjection_eq T hT, hr]
  change ContinuousLinearMap.id ℝ F - A.range.starProjection = A.ker.starProjection
  rw [← Submodule.starProjection_orthogonal]
  simp only [A.orthogonal_range, hA.adjoint_eq]

theorem contDiffOn_gramProjection (T : W → E →L[ℝ] F) (U : Set W)
    (hT : ContDiffOn ℝ ∞ T U)
    (hu : ∀ x ∈ U, IsUnit ((T x).adjoint.comp (T x))) :
    ContDiffOn ℝ ∞ (fun x => gramProjection (T x)) U := by
  have hadj : ContDiff ℝ ∞ (fun A : E →L[ℝ] F => A.adjoint) :=
    (ContinuousLinearMap.adjoint : (E →L[ℝ] F) ≃ₗᵢ[ℝ] (F →L[ℝ] E)).contDiff
  have htadj : ContDiffOn ℝ ∞ (fun x => (T x).adjoint) U := hadj.comp_contDiffOn hT
  have hg := htadj.clm_comp hT
  have hi : ContDiffOn ℝ ∞ (fun x => Ring.inverse ((T x).adjoint.comp (T x))) U := by
    intro x hx
    exact ((contDiffAt_ringInverse ℝ (hu x hx).unit).congr_of_eventuallyEq
      (by exact Filter.Eventually.of_forall fun _ => rfl)).comp_contDiffWithinAt x
        (hg x hx)
  exact hT.clm_comp (hi.clm_comp htadj)

end Gram

end Paper256

end

end OAI
