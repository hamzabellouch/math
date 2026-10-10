import OAI.Analysis.OperatorAlgebra.TracialTensorVector
import OAI.Analysis.Nuclearity.MinimalTensorExtension

namespace OAI

/-! Completion of a tracial tensor representation that is continuous for
the minimal tensor norm. -/

noncomputable section
open scoped TensorProduct ComplexOrder

namespace WeakPureInfiniteness

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (f : A →ₚ[ℂ] ℂ) (ht : ∀ a b, f (a * b) = f (b * a))
  (hn : ∀ z : A ⊗[ℂ] Aᵐᵒᵖ, ‖traceTensor f ht z‖ ≤ ‖minimalAlgebraicLinear z‖)

omit [PartialOrder A] [StarOrderedRing A] in
lemma tracialTensorAlgebraic_mul (z w : A ⊗[ℂ] Aᵐᵒᵖ) :
    minimalAlgebraicLinear (z * w) = minimalAlgebraicLinear z * minimalAlgebraicLinear w := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    induction w using TensorProduct.inductionOn with
    | tmul c d =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, minimalAlgebraicLinear_tmul,
        minimalElementary_mul]
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]

omit [PartialOrder A] [StarOrderedRing A] in
lemma tracialTensorAlgebraic_star (z : A ⊗[ℂ] Aᵐᵒᵖ) :
    minimalAlgebraicLinear (star z) = star (minimalAlgebraicLinear z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [TensorProduct.star_tmul, minimalAlgebraicLinear_tmul, minimalElementary_star]
  | add x y hx hy => simp only [star_add, map_add, hx, hy]

@[irreducible] def tracialTensorMinimal :
    MinimalTensor A Aᵐᵒᵖ →⋆ₙₐ[ℂ] (f.GNS →L[ℂ] f.GNS) :=
  denseLinearStarCompletion (minimalAlgebraicLinear (A := A) (B := Aᵐᵒᵖ))
    (traceTensor f ht).toLinearMap minimalAlgebraicLinear_dense
    tracialTensorAlgebraic_mul (fun x y => map_mul (traceTensor f ht) x y)
    tracialTensorAlgebraic_star (fun x => map_star (traceTensor f ht) x) hn

lemma tracialTensorMinimal_algebraic (z : A ⊗[ℂ] Aᵐᵒᵖ) :
    tracialTensorMinimal f ht hn (minimalAlgebraicLinear z) = traceTensor f ht z := by
  unfold tracialTensorMinimal
  exact denseLinearStarCompletion_apply _ _ _ _ _ _ _ _ z

lemma traceTensor_elementary (a b : A) :
    traceTensor f ht (a ⊗ₜ[ℂ] MulOpposite.op b) =
      f.gnsStarAlgHom a * NuclearTrace.rightGNS f ht (MulOpposite.op b) := by
  unfold traceTensor
  rfl

@[simp] lemma tracialTensorMinimal_elementary (a b : A) :
    tracialTensorMinimal f ht hn (minimalElementary a (MulOpposite.op b)) =
      f.gnsStarAlgHom a * NuclearTrace.rightGNS f ht (MulOpposite.op b) := by
  rw [← minimalAlgebraicLinear_tmul, tracialTensorMinimal_algebraic,
    traceTensor_elementary]

end WeakPureInfiniteness

end

end OAI
