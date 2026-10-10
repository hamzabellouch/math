import OAI.Analysis.KadisonKastler.L2TensorCoordinates

namespace OAI

/-! # Extending tensor intertwining identities by density -/

namespace KadisonKastler

open MeasureTheory
open scoped TensorProduct

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem l2ScalarSwap_intertwines_of_tensor (μ : Measure X) (ν : Measure Y)
    (A : Lp (Lp ℂ 2 ν) 2 μ →L[ℂ] Lp (Lp ℂ 2 ν) 2 μ)
    (B : Lp (Lp ℂ 2 μ) 2 ν →L[ℂ] Lp (Lp ℂ 2 μ) 2 ν)
    (h : ∀ f v, l2ScalarSwap μ ν (A (scalarLpTensor μ f v)) = B (scalarLpTensor ν v f))
    (F : Lp (Lp ℂ 2 ν) 2 μ) :
    l2ScalarSwap μ ν (A F) = B (l2ScalarSwap μ ν F) := by
  let S := l2ScalarSwap μ ν
  refine (l2TensorEmbedding_dense μ).induction_on
    (p := fun F => S (A F) = B (S F)) F ?_ ?_
  · exact isClosed_eq (S.continuous.comp A.continuous) (B.continuous.comp S.continuous)
  · intro z
    induction z using TensorProduct.inductionOn with
    | tmul f v =>
        change S (A (scalarLpTensor μ f v)) = B (S (scalarLpTensor μ f v))
        exact (h f v).trans (congrArg B (l2ScalarSwap_tensor μ ν f v).symm)
    | add z w hz hw =>
        change S (A (l2TensorEmbedding μ z)) = B (S (l2TensorEmbedding μ z)) at hz
        change S (A (l2TensorEmbedding μ w)) = B (S (l2TensorEmbedding μ w)) at hw
        simpa only [map_add] using congrArg₂ (· + ·) hz hw

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem intertwines_unitary_star (L : E →L[ℂ] F)
    (A : unitary (E →L[ℂ] E)) (B : unitary (F →L[ℂ] F))
    (h : ∀ x, L ((A : E →L[ℂ] E) x) = (B : F →L[ℂ] F) (L x)) (x : E) :
    L ((star A : E →L[ℂ] E) x) = (star B : F →L[ℂ] F) (L x) := by
  have hi : (A : E →L[ℂ] E) ((star A : E →L[ℂ] E) x) = x :=
    congrArg (fun T : E →L[ℂ] E => T x) (Unitary.mul_star_self_of_mem A.property)
  have he := h ((star A : E →L[ℂ] E) x)
  rw [hi] at he
  have hj : (star B : F →L[ℂ] F) ((B : F →L[ℂ] F) (L ((star A : E →L[ℂ] E) x))) =
      L ((star A : E →L[ℂ] E) x) :=
    congrArg (fun T : F →L[ℂ] F => T (L ((star A : E →L[ℂ] E) x)))
      (Unitary.star_mul_self_of_mem B.property)
  exact (congrArg (fun y => (star B : F →L[ℂ] F) y) he).trans hj |>.symm

end

end KadisonKastler

end OAI
