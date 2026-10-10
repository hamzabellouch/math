import OAI.Analysis.OperatorAlgebra.TracialTensorVector
import OAI.Analysis.OperatorAlgebra.GNSBundledOperators

namespace OAI

/-! The algebraic tracial representation on finite tensor sums. -/
noncomputable section
open scoped TensorProduct ComplexOrder
namespace WeakPureInfiniteness

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma traceTensor_sum (f : A →ₚ[ℂ] ℂ) (ht : ∀ a b, f (a * b) = f (b * a))
    {I : Type*} [Fintype I] (a b : I → A) :
    traceTensor f ht (∑ i, a i ⊗ₜ[ℂ] MulOpposite.op (b i)) =
      ∑ i, f.gnsStarAlgHom (a i) * NuclearTrace.rightGNS f ht (MulOpposite.op (b i)) := by
  unfold traceTensor
  simp only [map_sum, Pureness.commutingStarTensorHom_tmul]

lemma norm_traceTensor_sum (f : A →ₚ[ℂ] ℂ) (ht : ∀ a b, f (a * b) = f (b * a))
    {I : Type*} [Fintype I] (a b : I → A) :
    ‖traceTensor f ht (∑ i, a i ⊗ₜ[ℂ] MulOpposite.op (b i))‖ =
      ‖∑ i, gnsBundledLeft f (a i) * gnsBundledRight f ht (b i)‖ := by
  rw [traceTensor_sum]
  rfl

end WeakPureInfiniteness

end

end OAI
