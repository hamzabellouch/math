import Mathlib
import OAI.Analysis.WeakInfiniteness.InvariantSubspaces

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma RepresentationIrreducible.cyclic {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (hπ : RepresentationIrreducible π) {ξ : H} (hξ : ξ ≠ 0) :
    DenseRange (fun a : A => π a ξ) := by
  let l : A →ₗ[ℂ] H :=
    { toFun := fun a => π a ξ
      map_add' := by intro a b; simp
      map_smul' := by intro r a; simp }
  let S := l.range.topologicalClosure
  have hS : RepresentationInvariant π S := by
    intro a x hx
    change π a x ∈ closure (l.range : Set H)
    apply map_mem_closure (π a).continuous hx
    rintro _ ⟨b,rfl⟩
    exact ⟨a*b,by simp [l,map_mul]⟩
  obtain hs | hs := hπ S l.range.isClosed_topologicalClosure hS
  · have hm : ξ ∈ S := l.range.le_topologicalClosure ⟨1,by simp [l]⟩
    rw [hs,Submodule.mem_bot] at hm
    exact (hξ hm).elim
  · change Dense (l.range : Set H)
    exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hs

lemma RepresentationIrreducible.exists_mixed_nonzero {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (hπ : RepresentationIrreducible π) {u v : A} (hu : π u ≠ 0) (hv : π v ≠ 0) :
    ∃ x : A,π (u*x*v) ≠ 0 := by
  by_contra! hn
  obtain ⟨ξ,hξ⟩ : ∃ ξ : H,π v ξ ≠ 0 := by
    by_contra! h
    exact hv (by ext ξ; exact h ξ)
  have hz : ∀ η : H,π u η=0 := isClosed_property (hπ.cyclic hξ)
    (isClosed_eq (π u).continuous continuous_const) (by
      intro a
      have hh := DFunLike.congr_fun (hn a) ξ
      simpa only [map_mul,mul_apply_eq_comp,zero_apply] using hh)
  exact hu (by ext η; exact hz η)

end

end WeakPureInfiniteness
end

end OAI
