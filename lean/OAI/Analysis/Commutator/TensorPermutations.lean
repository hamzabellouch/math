import Mathlib

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

section Gram

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem inner_linearCombination_eq (a : ι → E) (b : ι → F)
    (h : ∀ i j, inner ℂ (b i) (b j) = inner ℂ (a i) (a j))
    (x y : ι →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ b x) (Finsupp.linearCombination ℂ b y) =
      inner ℂ (Finsupp.linearCombination ℂ a x) (Finsupp.linearCombination ℂ a y) := by
  classical
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, h]

def gramIsometry (a : ι → E) (b : ι → F)
    (ha : Submodule.span ℂ (Set.range a) = ⊤)
    (h : ∀ i j, inner ℂ (b i) (b j) = inner ℂ (a i) (a j)) : E →ₗᵢ[ℂ] F := by
  let A := Finsupp.linearCombination ℂ a
  let B := Finsupp.linearCombination ℂ b
  have hA : Function.Surjective A := by
    apply LinearMap.range_eq_top.mp
    rwa [Finsupp.range_linearCombination]
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [inner_linearCombination_eq a b h]
    rw [LinearMap.mem_ker.mp hx]
    simp
  let f := (LinearMap.ker A).liftQ B hker |>.comp
    (A.quotKerEquivOfSurjective hA).symm.toLinearMap
  have happ : ∀ x, f (A x) = B x := by
    intro x
    change (LinearMap.ker A).liftQ B hker
      ((A.quotKerEquivOfSurjective hA).symm (A x)) = B x
    have he : (A.quotKerEquivOfSurjective hA).symm (A x) =
        Submodule.Quotient.mk x := by
      apply (A.quotKerEquivOfSurjective hA).injective
      simp [LinearMap.quotKerEquivOfSurjective_apply_mk]
    rw [he, Submodule.liftQ_apply]
  refine ⟨f, ?_⟩
  apply (LinearMap.norm_map_iff_inner_map_map f).mpr
  intro x y
  obtain ⟨v, rfl⟩ := hA x
  obtain ⟨w, rfl⟩ := hA y
  rw [happ, happ]
  exact inner_linearCombination_eq a b h v w

@[simp] theorem gramIsometry_apply (a : ι → E) (b : ι → F)
    (ha : Submodule.span ℂ (Set.range a) = ⊤)
    (h : ∀ i j, inner ℂ (b i) (b j) = inner ℂ (a i) (a j)) (i : ι) :
    gramIsometry a b ha h (a i) = b i := by
  classical
  unfold gramIsometry
  dsimp
  have hA : Function.Surjective (Finsupp.linearCombination ℂ a) := by
    apply LinearMap.range_eq_top.mp
    rwa [Finsupp.range_linearCombination]
  have he : ((Finsupp.linearCombination ℂ a).quotKerEquivOfSurjective hA).symm
      (a i) = Submodule.Quotient.mk (Finsupp.single i 1) := by
    apply ((Finsupp.linearCombination ℂ a).quotKerEquivOfSurjective hA).injective
    simp [LinearMap.quotKerEquivOfSurjective_apply_mk]
  rw [he, Submodule.liftQ_apply]
  simp

end Gram

end Kadison
end

end OAI
