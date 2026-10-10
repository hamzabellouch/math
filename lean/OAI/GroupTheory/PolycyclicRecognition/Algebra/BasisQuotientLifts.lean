import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # A basis adapted to specified quotient lifts -/

noncomputable section
namespace PolycyclicRecognition

open Module Set

variable {𝕜 : Type*} [Field 𝕜]

variable {V I J : Type*} [AddCommGroup V] [Module 𝕜 V] (U : Submodule 𝕜 V)
  (bU : Basis I 𝕜 U) (bQ : Basis J 𝕜 (V ⧸ U))
  (lift : J → V) (hlift : ∀ j, U.mkQ (lift j) = bQ j)

def basisWithQuotientLifts : Basis (I ⊕ J) 𝕜 V := by
  let v : I ⊕ J → V := Sum.elim (fun i => (bU i : V)) lift
  apply Basis.mk (v := v)
  · apply LinearIndependent.sumElim_of_quotient
    · exact bU.linearIndependent
    · change LinearIndependent 𝕜 (fun j => U.mkQ (lift j))
      simpa only [hlift] using bQ.linearIndependent
  · dsimp only [v]
    rw [Set.Sum.elim_range, Submodule.span_union,
      show range (fun i => (bU i : V)) = U.subtype '' range bU by
        ext x; simp only [mem_range, mem_image]; aesop,
      ← Submodule.map_span, bU.span_eq, Submodule.map_top, Submodule.range_subtype,
      top_le_iff, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
    simpa only [Function.comp_def, hlift] using bQ.span_eq

@[simp] theorem basisWithQuotientLifts_inl (i : I) :
    basisWithQuotientLifts U bU bQ lift hlift (Sum.inl i) = (bU i : V) := by
  simp only [basisWithQuotientLifts, Basis.coe_mk, Sum.elim_inl]

@[simp] theorem basisWithQuotientLifts_inr (j : J) :
    basisWithQuotientLifts U bU bQ lift hlift (Sum.inr j) = lift j := by
  simp only [basisWithQuotientLifts, Basis.coe_mk, Sum.elim_inr]

theorem basisWithQuotientLifts_repr_inl (v : U) (i : I) :
    (basisWithQuotientLifts U bU bQ lift hlift).repr (v : V) (Sum.inl i) = bU.repr v i := by
  classical
  let b := basisWithQuotientLifts U bU bQ lift hlift
  have hf : (b.coord (Sum.inl i)).comp U.subtype = bU.coord i := by
    apply bU.ext
    intro j
    change b.repr (bU j : V) (Sum.inl i) = bU.repr (bU j) i
    rw [← basisWithQuotientLifts_inl U bU bQ lift hlift j]
    simp only [b, Basis.repr_self, Finsupp.single_apply, Sum.inl.injEq]
  exact congrArg (fun f : U →ₗ[𝕜] 𝕜 => f v) hf

theorem basisWithQuotientLifts_repr_inr (v : V) (j : J) :
    (basisWithQuotientLifts U bU bQ lift hlift).repr v (Sum.inr j) =
      bQ.repr (U.mkQ v) j := by
  classical
  let b := basisWithQuotientLifts U bU bQ lift hlift
  have hf : b.coord (Sum.inr j) = (bQ.coord j).comp U.mkQ := by
    apply b.ext
    intro k
    cases k with
    | inl i =>
      change b.repr (b (Sum.inl i)) (Sum.inr j) = bQ.repr (U.mkQ (b (Sum.inl i))) j
      rw [Basis.repr_self]
      have hz : U.mkQ (b (Sum.inl i)) = 0 := by
        rw [basisWithQuotientLifts_inl]
        exact (Submodule.Quotient.mk_eq_zero U).mpr (bU i).property
      rw [hz, map_zero]
      simp
    | inr i =>
      change b.repr (b (Sum.inr i)) (Sum.inr j) = bQ.repr (U.mkQ (b (Sum.inr i))) j
      rw [Basis.repr_self, basisWithQuotientLifts_inr, hlift, Basis.repr_self]
      simp only [Finsupp.single_apply, Sum.inr.injEq]
  exact congrArg (fun f : V →ₗ[𝕜] 𝕜 => f v) hf

end PolycyclicRecognition

end

end OAI
