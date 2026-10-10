import OAI.Analysis.Pureness.Operators.CStarHomClosedRange
import Mathlib.Topology.Algebra.Module.Basic

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped CStarAlgebra
variable {R S E : Type*} [Ring R] [StarAddMonoid R] [Algebra ℂ R]
variable [Ring S] [StarAddMonoid S] [Algebra ℂ S] [CStarAlgebra E]
variable (f : R →⋆ₐ[ℂ] E) (g : R →⋆ₐ[ℂ] S)

def denseKernelImage : Submodule ℂ E := g.toLinearMap.ker.map f.toLinearMap

lemma denseKernelImage_mem (x : E) :
    x ∈ denseKernelImage f g ↔ ∃ z : R, g z = 0 ∧ f z = x := Iff.rfl

lemma denseKernelImage_mul_left (a : R) {x : E} (hx : x ∈ denseKernelImage f g) :
    f a * x ∈ denseKernelImage f g := by
  obtain ⟨z, hz, rfl⟩ := hx
  change g z = 0 at hz
  exact ⟨a*z, by change g (a*z) = 0; rw [map_mul, hz, mul_zero], map_mul f a z⟩

lemma denseKernelImage_mul_right (a : R) {x : E} (hx : x ∈ denseKernelImage f g) :
    x * f a ∈ denseKernelImage f g := by
  obtain ⟨z, hz, rfl⟩ := hx
  change g z = 0 at hz
  exact ⟨z*a, by change g (z*a) = 0; rw [map_mul, hz, zero_mul], map_mul f z a⟩

lemma denseKernelImage_star {x : E} (hx : x ∈ denseKernelImage f g) :
    star x ∈ denseKernelImage f g := by
  obtain ⟨z, hz, rfl⟩ := hx
  change g z = 0 at hz
  exact ⟨star z, by change g (star z) = 0; rw [map_star, hz, star_zero], map_star f z⟩

variable (hf : DenseRange f)

include hf in
lemma denseKernelClosure_mul_left (a : E) {x : E}
    (hx : x ∈ (denseKernelImage f g).topologicalClosure) :
    a*x ∈ (denseKernelImage f g).topologicalClosure := by
  refine hf.induction_on a
    ((denseKernelImage f g).isClosed_topologicalClosure.preimage (continuous_id.mul continuous_const)) ?_
  intro b
  refine closure_minimal ?_
    ((denseKernelImage f g).isClosed_topologicalClosure.preimage (continuous_const.mul continuous_id)) hx
  intro y hy
  exact (denseKernelImage f g).le_topologicalClosure (denseKernelImage_mul_left f g b hy)

include hf in
lemma denseKernelClosure_mul_right (a : E) {x : E}
    (hx : x ∈ (denseKernelImage f g).topologicalClosure) :
    x*a ∈ (denseKernelImage f g).topologicalClosure := by
  refine hf.induction_on a
    ((denseKernelImage f g).isClosed_topologicalClosure.preimage (continuous_const.mul continuous_id)) ?_
  intro b
  refine closure_minimal ?_
    ((denseKernelImage f g).isClosed_topologicalClosure.preimage (continuous_id.mul continuous_const)) hx
  intro y hy
  exact (denseKernelImage f g).le_topologicalClosure (denseKernelImage_mul_right f g b hy)

def denseKernelClosedIdeal : ClosedStarIdeal E where
  ideal := TwoSidedIdeal.mk' ((denseKernelImage f g).topologicalClosure : Set E)
    (denseKernelImage f g).topologicalClosure.zero_mem
    (fun {_ _} hx hy => (denseKernelImage f g).topologicalClosure.add_mem hx hy)
    (fun {_} hx => (denseKernelImage f g).topologicalClosure.neg_mem hx)
    (fun {a _} hx => denseKernelClosure_mul_left f g hf a hx)
    (fun {_ a} hx => denseKernelClosure_mul_right f g hf a hx)
  star_mem := by
    intro x hx
    simp only [TwoSidedIdeal.mem_mk'] at hx ⊢
    refine closure_minimal ?_
      ((denseKernelImage f g).isClosed_topologicalClosure.preimage continuous_star) hx
    intro y hy
    exact (denseKernelImage f g).le_topologicalClosure (denseKernelImage_star f g hy)
  isClosed := by
    rw [TwoSidedIdeal.coe_mk']
    exact (denseKernelImage f g).isClosed_topologicalClosure

lemma denseKernelClosedIdeal_coe :
    ((denseKernelClosedIdeal f g hf).ideal : Set E) =
      closure {x | ∃ z : R, g z = 0 ∧ f z = x} := by
  simp only [denseKernelClosedIdeal, TwoSidedIdeal.coe_mk']
  rfl

lemma denseKernelClosedIdeal_mem (x : E) :
    x ∈ (denseKernelClosedIdeal f g hf).ideal ↔
      x ∈ (denseKernelImage f g).topologicalClosure :=
  by
    simp only [denseKernelClosedIdeal, TwoSidedIdeal.mem_mk']
    rfl

variable {F : Type*} [CStarAlgebra F]

lemma denseKernelClosedIdeal_map_zero (L : E →⋆ₐ[ℂ] F) (k : S →⋆ₐ[ℂ] F)
    (hL : ∀ z, L (f z) = k (g z)) (x : E)
    (hx : x ∈ (denseKernelClosedIdeal f g hf).ideal) : L x = 0 := by
  change x ∈ ((denseKernelClosedIdeal f g hf).ideal : Set E) at hx
  rw [denseKernelClosedIdeal_coe] at hx
  refine closure_minimal ?_ (isClosed_eq (map_continuous L) continuous_const) hx
  rintro y ⟨z, hz, rfl⟩
  change L (f z) = 0
  rw [hL, hz, map_zero]
end CuntzPureness

end

end OAI
