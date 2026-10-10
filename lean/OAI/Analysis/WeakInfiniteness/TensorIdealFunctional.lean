import Mathlib
import OAI.Analysis.WeakInfiniteness.AlgebraicTensorSpan
import OAI.Analysis.WeakInfiniteness.TensorFunctoriality

namespace OAI

universe u v

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section ClosedTensorIdeal

variable {A : Type u} {B C : Type v}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

lemma tensorFunctional_vanishes_ideal (q : B →⋆ₙₐ[ℂ] C)
    (φ : MinimalTensor A B →L[ℂ] ℂ)
    (hφ : ∀ a b, q b = 0 → φ (minimalElementary a b) = 0)
    (x : MinimalTensor A B) (hx : x.val ∈ tensorKernelIdeal (A := A) q) : φ x = 0 := by
  have hs : ∀ y ∈ Submodule.span ℂ
      {z : SpatialAmbient A B | ∃ a : A, ∃ b : B, q b = 0 ∧ z = spatialElementary a b},
      ∃ z : MinimalTensor A B, z.val = y ∧ φ z = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a,b,hb,rfl⟩ := hy
      exact ⟨minimalElementary a b, rfl, hφ a b hb⟩
    | zero => exact ⟨0, rfl, map_zero φ⟩
    | add y w _ _ hy hw =>
      obtain ⟨z,rfl,hz⟩ := hy
      obtain ⟨v,rfl,hv⟩ := hw
      exact ⟨z+v, rfl, by rw [map_add,hz,hv,add_zero]⟩
    | smul c y _ hy =>
      obtain ⟨z,rfl,hz⟩ := hy
      exact ⟨c • z, rfl, by rw [map_smul,hz,smul_zero]⟩
  by_contra hn
  have hp : 0 < ‖φ x‖ := norm_pos_iff.mpr hn
  have hC : 0 < ‖φ‖ + 1 := by positivity
  change x.val ∈ (tensorKernelIdeal (A := A) q : Set (SpatialAmbient A B)) at hx
  rw [tensorKernelIdeal_eq_closure_span] at hx
  obtain ⟨y,hy,hd⟩ := Metric.mem_closure_iff.mp hx (‖φ x‖ / (‖φ‖ + 1)) (div_pos hp hC)
  obtain ⟨z,rfl,hz⟩ := hs y hy
  have hd' : ‖x-z‖ < ‖φ x‖ / (‖φ‖ + 1) := by
    change ‖x.val-z.val‖ < _
    simpa only [dist_eq_norm] using hd
  have he : φ (x-z) = φ x := by rw [map_sub,hz,sub_zero]
  have hbound : ‖φ x‖ ≤ (‖φ‖ + 1) * ‖x-z‖ := by
    rw [← he]
    exact (φ.le_opNorm (x-z)).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hlt : (‖φ‖ + 1) * ‖x-z‖ < ‖φ x‖ := by
    exact (mul_lt_mul_of_pos_left hd' hC).trans_eq (mul_div_cancel₀ _ (ne_of_gt hC))
  exact (not_lt_of_ge hbound) hlt

lemma exact_functional_kernel {A B C : Type u}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    (hA : Exact A) (q : B →⋆ₙₐ[ℂ] C) (hq : Function.Surjective q)
    (φ : MinimalTensor A B →L[ℂ] ℂ)
    (hφ : ∀ a b, q b = 0 → φ (minimalElementary a b) = 0)
    (x : MinimalTensor A B) (hx : minimalMapRight q x = 0) : φ x = 0 := by
  apply tensorFunctional_vanishes_ideal q φ hφ x
  apply hA B C q hq x
  intro π
  exact congrArg (fun y : MinimalTensor A C => y.val π) hx

end ClosedTensorIdeal

end WeakPureInfiniteness
end

end OAI
