import Mathlib
import OAI.Analysis.Commutator.TensorPermutations

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison

section GramEquiv

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem gramIsometry_surjective (a : ι → E) (b : ι → F)
    (ha : Submodule.span ℂ (Set.range a) = ⊤)
    (hb : Submodule.span ℂ (Set.range b) = ⊤)
    (h : ∀ i j, inner ℂ (b i) (b j) = inner ℂ (a i) (a j)) :
    Function.Surjective (gramIsometry a b ha h) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hb]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨a i, gramIsometry_apply a b ha h i⟩

def gramEquiv (a : ι → E) (b : ι → F)
    (ha : Submodule.span ℂ (Set.range a) = ⊤)
    (hb : Submodule.span ℂ (Set.range b) = ⊤)
    (h : ∀ i j, inner ℂ (b i) (b j) = inner ℂ (a i) (a j)) : E ≃ₗᵢ[ℂ] F :=
  LinearIsometryEquiv.ofSurjective (gramIsometry a b ha h)
    (gramIsometry_surjective a b ha hb h)

@[simp] theorem gramEquiv_apply (a : ι → E) (b : ι → F)
    (ha : Submodule.span ℂ (Set.range a) = ⊤)
    (hb : Submodule.span ℂ (Set.range b) = ⊤)
    (h : ∀ i j, inner ℂ (b i) (b j) = inner ℂ (a i) (a j)) (i : ι) :
    gramEquiv a b ha hb h (a i) = b i := gramIsometry_apply a b ha h i

end GramEquiv

end Kadison
end

end OAI
