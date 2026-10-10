import OAI.Analysis.Pureness.Tensor.CommutingTensorCoefficients
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct
variable {A B N : Type*} [NormedRing A] [CompleteSpace A] [Nontrivial A]
variable [NormedAlgebra ℂ A] [Ring B] [Algebra ℂ B] [Ring N] [Algebra ℂ N]

theorem commutingAlgTensorHom_injective (hsimple : TopologicallySimple A)
    (φ : A →ₐ[ℂ] N) (ψ : B →ₐ[ℂ] N) (hψ : Function.Injective ψ)
    (hc : ∀ a b, Commute (φ a) (ψ b)) :
    Function.Injective (Algebra.TensorProduct.lift φ ψ hc) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  let b := Module.Free.chooseBasis ℂ B
  obtain ⟨a,rfl⟩ := TensorProduct.eq_repr_basis_right b z
  have hr : ∑ i ∈ a.support, φ (a i)*ψ (b i)=0 := by
    simpa only [Finsupp.sum,map_sum,Algebra.TensorProduct.lift_tmul] using hz
  have ha := commuting_relation_coefficients_zero φ ψ hc hsimple
    hψ b b.linearIndependent a.support a hr
  change ∑ i ∈ a.support, a i ⊗ₜ[ℂ] b i = 0
  apply Finset.sum_eq_zero
  intro i hi
  rw [ha i hi,TensorProduct.zero_tmul]
end CuntzPureness

end

end OAI
