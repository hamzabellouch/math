import OAI.Analysis.BoundedHochschild.RightAveragingAlgebra
import OAI.Analysis.BoundedHochschild.WeakOperatorCompactness

namespace OAI

/-! The elementary right-averaging actions are continuous for pointwise
weak-star convergence. Multiplication normality is used only in the output
variable; the maps being averaged need not themselves be normal. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M X : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Transport a bounded linear operator to the weak dual. -/
def weakDualOperator (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (L : M →L[ℂ] M)
    (F : WeakDual ℂ X) : WeakDual ℂ X :=
  StrongDual.toWeakDual (e.symm (L (e (WeakDual.toStrongDual F))))

lemma weakDualOperator_image (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (L : M →L[ℂ] M) (a : M) :
    weakDualOperator e L (StrongDual.toWeakDual (e.symm a)) =
      StrongDual.toWeakDual (e.symm (L a)) := by
  change StrongDual.toWeakDual (e.symm (L (e (e.symm a)))) = _
  rw [e.apply_symm_apply]

lemma weakDualOperator_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (L : M →L[ℂ] M) (hL : HasPreadjoint e L) : Continuous (weakDualOperator e L) := by
  apply WeakDual.continuous_of_continuous_eval
  intro x
  obtain ⟨y, hy⟩ := hL x
  have h : (fun F : WeakDual ℂ X => weakDualOperator e L F x) = fun F => F y := by
    funext F
    simp only [weakDualOperator, StrongDual.toWeakDual_apply, hy, e.symm_apply_apply,
      WeakDual.toStrongDual_apply]
  rw [h]
  exact WeakDual.eval_continuous y

/-- Right averaging acts on the ambient space of all weak-dual-valued
functions, so its continuity also applies to closures of operator families. -/
def weakRightAverage {I : Type*} [Fintype I] (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (m : I → M) (F : M → WeakDual ℂ X) : M → WeakDual ℂ X := fun a =>
  ∑ i, weakDualOperator e ((ContinuousLinearMap.mul ℂ M).flip (star (m i))) (F (a * m i))

lemma weakRightAverage_image {I : Type*} [Fintype I]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (m : I → M) (T : M →L[ℂ] M) :
    weakRightAverage e m (weakOperatorImage e T) =
      weakOperatorImage e (finiteRightAverage m T) := by
  funext a
  simp only [weakRightAverage, weakOperatorImage, weakDualOperator_image,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
    finiteRightAverage_apply, map_sum]

variable [CompleteSpace X]

lemma weakRightAverage_continuous {I : Type*} [Fintype I]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (m : I → M) : Continuous (weakRightAverage e m) := by
  apply continuous_pi
  intro a
  apply continuous_finsetSum
  intro i _
  exact (weakDualOperator_continuous e _
    ((HochschildSakai.abstract_multiplication_normal e).2 (star (m i)))).comp
      (continuous_apply (a * m i))

end BoundedHochschild.KadisonRingrose

end

end OAI
