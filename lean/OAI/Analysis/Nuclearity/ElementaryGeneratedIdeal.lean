import OAI.Analysis.WeakInfiniteness.TensorAbsorption
import OAI.Analysis.JiangSu.Nonunital.ClosedIdealBasic

namespace OAI

/-! The closed span of the elementary tensors in a closed tensor ideal is
itself an ideal. This does not assert that it is the whole original ideal. -/

noncomputable section
open scoped Topology

namespace WeakPureInfiniteness

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def elementaryIdealSpan (J : NonunitalClosedIdeal.Ideal (MinimalTensor A B)) :
    Submodule ℂ (MinimalTensor A B) :=
  Submodule.span ℂ {z | ∃ a b, z = minimalElementary a b ∧ z ∈ J.module}

private lemma elementaryIdealSpan_mul_left (J : NonunitalClosedIdeal.Ideal (MinimalTensor A B))
    (a : A) (b : B) {x : MinimalTensor A B} (hx : x ∈ elementaryIdealSpan J) :
    minimalElementary a b * x ∈ elementaryIdealSpan J := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, d, rfl, hx⟩ := hx
    apply Submodule.subset_span
    exact ⟨a * c, b * d, (minimalElementary_mul a c b d).symm, J.mul_left _ _ hx⟩
  | zero => simpa only [mul_zero] using (elementaryIdealSpan J).zero_mem
  | add x y _ _ hx hy => simpa only [mul_add] using (elementaryIdealSpan J).add_mem hx hy
  | smul z x _ hx => simpa only [mul_smul_comm] using (elementaryIdealSpan J).smul_mem z hx

private lemma elementaryIdealSpan_mul_right (J : NonunitalClosedIdeal.Ideal (MinimalTensor A B))
    (a : A) (b : B) {x : MinimalTensor A B} (hx : x ∈ elementaryIdealSpan J) :
    x * minimalElementary a b ∈ elementaryIdealSpan J := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, d, rfl, hx⟩ := hx
    apply Submodule.subset_span
    exact ⟨c * a, d * b, (minimalElementary_mul c a d b).symm, J.mul_right _ _ hx⟩
  | zero => simpa only [zero_mul] using (elementaryIdealSpan J).zero_mem
  | add x y _ _ hx hy => simpa only [add_mul] using (elementaryIdealSpan J).add_mem hx hy
  | smul z x _ hx => simpa only [smul_mul_assoc] using (elementaryIdealSpan J).smul_mem z hx

private lemma elementaryIdealSpan_star (J : NonunitalClosedIdeal.Ideal (MinimalTensor A B))
    {x : MinimalTensor A B} (hx : x ∈ elementaryIdealSpan J) :
    star x ∈ elementaryIdealSpan J := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, rfl, hx⟩ := hx
    apply Submodule.subset_span
    exact ⟨star a, star b, (minimalElementary_star a b).symm, J.star_mem _ hx⟩
  | zero => simpa only [star_zero] using (elementaryIdealSpan J).zero_mem
  | add x y _ _ hx hy => simpa only [star_add] using (elementaryIdealSpan J).add_mem hx hy
  | smul z x _ hx => simpa only [star_smul] using (elementaryIdealSpan J).smul_mem (star z) hx

def elementaryGeneratedIdeal (J : NonunitalClosedIdeal.Ideal (MinimalTensor A B)) :
    NonunitalClosedIdeal.Ideal (MinimalTensor A B) where
  module := (elementaryIdealSpan J).topologicalClosure
  closed := (elementaryIdealSpan J).isClosed_topologicalClosure
  mul_left a x hx := by
    let K := (elementaryIdealSpan J).topologicalClosure
    have hK : IsClosed (K : Set (MinimalTensor A B)) :=
      (elementaryIdealSpan J).isClosed_topologicalClosure
    let L := K.comap ((ContinuousLinearMap.mul ℂ (MinimalTensor A B)).flip x).toLinearMap
    have hL : IsClosed (L : Set (MinimalTensor A B)) :=
      hK.preimage ((ContinuousLinearMap.mul ℂ (MinimalTensor A B)).flip x).continuous
    have ht : L = ⊤ := by
      apply minimal_elementary_span_dense L hL
      intro c d
      change minimalElementary c d * x ∈ K
      apply closure_minimal (t := {y | minimalElementary c d * y ∈ K}) ?_
        (hK.preimage (continuous_const.mul continuous_id)) hx
      intro y hy
      exact (elementaryIdealSpan J).le_topologicalClosure (elementaryIdealSpan_mul_left J c d hy)
    change a ∈ L
    rw [ht]
    trivial
  mul_right x a hx := by
    let K := (elementaryIdealSpan J).topologicalClosure
    have hK : IsClosed (K : Set (MinimalTensor A B)) :=
      (elementaryIdealSpan J).isClosed_topologicalClosure
    let L := K.comap (ContinuousLinearMap.mul ℂ (MinimalTensor A B) x).toLinearMap
    have hL : IsClosed (L : Set (MinimalTensor A B)) :=
      hK.preimage (ContinuousLinearMap.mul ℂ (MinimalTensor A B) x).continuous
    have ht : L = ⊤ := by
      apply minimal_elementary_span_dense L hL
      intro c d
      change x * minimalElementary c d ∈ K
      apply closure_minimal (t := {y | y * minimalElementary c d ∈ K}) ?_
        (hK.preimage (continuous_id.mul continuous_const)) hx
      intro y hy
      exact (elementaryIdealSpan J).le_topologicalClosure (elementaryIdealSpan_mul_right J c d hy)
    change a ∈ L
    rw [ht]
    trivial
  star_mem x hx := by
    apply closure_minimal (t := {y | star y ∈ (elementaryIdealSpan J).topologicalClosure}) ?_
      ((elementaryIdealSpan J).isClosed_topologicalClosure.preimage continuous_star) hx
    intro y hy
    exact (elementaryIdealSpan J).le_topologicalClosure (elementaryIdealSpan_star J hy)

theorem elementaryGeneratedIdeal_le (J : NonunitalClosedIdeal.Ideal (MinimalTensor A B)) :
    (elementaryGeneratedIdeal J).module ≤ J.module := by
  apply closure_minimal ?_ J.closed
  apply Submodule.span_le.mpr
  rintro x ⟨a, b, _, hx⟩
  exact hx

theorem elementary_mem_generatedIdeal (J : NonunitalClosedIdeal.Ideal (MinimalTensor A B))
    (a : A) (b : B) (h : minimalElementary a b ∈ J.module) :
    minimalElementary a b ∈ (elementaryGeneratedIdeal J).module :=
  (elementaryIdealSpan J).le_topologicalClosure (Submodule.subset_span ⟨a, b, rfl, h⟩)

end WeakPureInfiniteness

end

end OAI
