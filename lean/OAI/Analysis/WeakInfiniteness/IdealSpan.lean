import Mathlib
import OAI.Analysis.WeakInfiniteness.Hereditary

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

open scoped CStarAlgebra Topology

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
def algebraicIdealSpan (h : A) : Submodule ℂ A :=
  Submodule.span ℂ (Set.range (fun p : A × A => p.1*h*p.2))

omit [PartialOrder A] [StarOrderedRing A] in
lemma algebraicIdealSpan_mul_left (h a : A) {x : A} (hx : x ∈ algebraicIdealSpan h) :
    a*x ∈ algebraicIdealSpan h := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨c,d⟩,rfl⟩ := hy
    exact Submodule.subset_span ⟨(a*c,d),by simp only [mul_assoc]⟩
  | zero => simpa only [mul_zero] using (algebraicIdealSpan h).zero_mem
  | add y z _ _ hy hz => simpa only [mul_add] using (algebraicIdealSpan h).add_mem hy hz
  | smul c y _ hy => simpa only [mul_smul_comm] using (algebraicIdealSpan h).smul_mem c hy

omit [PartialOrder A] [StarOrderedRing A] in
lemma algebraicIdealSpan_mul_right (h a : A) {x : A} (hx : x ∈ algebraicIdealSpan h) :
    x*a ∈ algebraicIdealSpan h := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨c,d⟩,rfl⟩ := hy
    exact Submodule.subset_span ⟨(c,d*a),by simp only [mul_assoc]⟩
  | zero => simpa only [zero_mul] using (algebraicIdealSpan h).zero_mem
  | add y z _ _ hy hz => simpa only [add_mul] using (algebraicIdealSpan h).add_mem hy hz
  | smul c y _ hy => simpa only [smul_mul_assoc] using (algebraicIdealSpan h).smul_mem c hy

omit [PartialOrder A] [StarOrderedRing A] in
lemma algebraicIdealSpan_star (h : A) (hh : IsSelfAdjoint h) {x : A}
    (hx : x ∈ algebraicIdealSpan h) : star x ∈ algebraicIdealSpan h := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨c,d⟩,rfl⟩ := hy
    exact Submodule.subset_span ⟨(star d,star c),by
      simp only [star_mul,hh.star_eq,mul_assoc]⟩
  | zero => simpa only [star_zero] using (algebraicIdealSpan h).zero_mem
  | add y z _ _ hy hz => simpa only [star_add] using (algebraicIdealSpan h).add_mem hy hz
  | smul c y _ hy => simpa only [star_smul] using (algebraicIdealSpan h).smul_mem (star c) hy

omit [PartialOrder A] [StarOrderedRing A] in
def algebraicIdealSubalgebra (h : A) (hh : IsSelfAdjoint h) : NonUnitalStarSubalgebra ℂ A where
  toSubmodule := algebraicIdealSpan h
  mul_mem' := fun {x _} _ hy => algebraicIdealSpan_mul_left h x hy
  star_mem' := algebraicIdealSpan_star h hh

def generatedClosedIdeal (h : A) (hh : IsSelfAdjoint h) : NonUnitalStarSubalgebra ℂ A :=
  (algebraicIdealSubalgebra h hh).topologicalClosure

instance (h : A) (hh : IsSelfAdjoint h) : IsClosed (generatedClosedIdeal h hh : Set A) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

instance (h : A) (hh : IsSelfAdjoint h) : CompleteSpace (generatedClosedIdeal h hh) :=
  (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).isComplete.completeSpace_coe

omit [PartialOrder A] [StarOrderedRing A] in
lemma generatedClosedIdeal_mul_left (h a : A) (hh : IsSelfAdjoint h) {x : A}
    (hx : x ∈ generatedClosedIdeal h hh) : a*x ∈ generatedClosedIdeal h hh := by
  apply closure_minimal _ ((NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage
    (continuous_const.mul continuous_id)) hx
  intro y hy
  exact (algebraicIdealSubalgebra h hh).le_topologicalClosure (algebraicIdealSpan_mul_left h a hy)

omit [PartialOrder A] [StarOrderedRing A] in
lemma generatedClosedIdeal_mul_right (h a : A) (hh : IsSelfAdjoint h) {x : A}
    (hx : x ∈ generatedClosedIdeal h hh) : x*a ∈ generatedClosedIdeal h hh := by
  apply closure_minimal _ ((NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage
    (continuous_id.mul continuous_const)) hx
  intro y hy
  exact (algebraicIdealSubalgebra h hh).le_topologicalClosure (algebraicIdealSpan_mul_right h a hy)

lemma hereditary_le_generatedClosedIdeal (h : A) (hh : IsSelfAdjoint h) :
    hereditarySubalgebra h hh ≤ generatedClosedIdeal h hh := by
  intro x hx
  apply closure_minimal _ (NonUnitalStarSubalgebra.isClosed_topologicalClosure _) hx
  rintro _ ⟨a,rfl⟩
  have ht : Filter.Tendsto (fun e : A => (h*a)*h*e) (CStarAlgebra.approximateUnit A)
      (𝓝 (h*a*h)) := (CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left _
  exact (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).mem_of_tendsto ht
    (Filter.Eventually.of_forall (fun e => (algebraicIdealSubalgebra h hh).le_topologicalClosure
      (Submodule.subset_span ⟨(h*a,e),rfl⟩)))

lemma self_mem_generatedClosedIdeal (h : A) (hh : 0 ≤ h) :
    h ∈ generatedClosedIdeal h hh.isSelfAdjoint :=
  hereditary_le_generatedClosedIdeal h hh.isSelfAdjoint (self_mem_hereditary h hh)

end

end WeakPureInfiniteness
end

end OAI
