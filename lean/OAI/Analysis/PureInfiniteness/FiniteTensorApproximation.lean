import OAI.Analysis.WeakInfiniteness.WordTensorDensity
import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorMap

namespace OAI

/-! Finite elementary sums approximating an element of the minimal tensor
product, in the form needed by simultaneous pure-state excision. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

universe u v
variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

theorem exists_finite_tensor_approximation (z : MinimalTensor A B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (I : Type (max u v)) (_ : Fintype I) (a : I → A) (b : I → B),
      ‖z - ∑ i, minimalElementary (a i) (b i)‖ < ε := by
  classical
  let S := Submodule.span ℂ (Set.range fun p : A × B => minimalElementary p.1 p.2)
  have hd : S.topologicalClosure = ⊤ := by
    apply minimal_elementary_span_dense _ S.isClosed_topologicalClosure
    intro a b
    exact S.le_topologicalClosure (Submodule.subset_span ⟨(a, b), rfl⟩)
  have hz : z ∈ closure (S : Set (MinimalTensor A B)) := by
    change z ∈ S.topologicalClosure
    rw [hd]
    trivial
  obtain ⟨y, hy, hzy⟩ := Metric.mem_closure_iff.mp hz ε hε
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
  refine ⟨↥c.support, inferInstance, (fun i => c i.val • i.val.1),
    (fun i => i.val.2), ?_⟩
  have he : (∑ i : ↥c.support, minimalElementary (c i.val • i.val.1) i.val.2) =
      c.sum (fun p t => t • minimalElementary p.1 p.2) := by
    simp only [minimalElementary_smul_left, Finsupp.sum]
    exact Finset.sum_coe_sort c.support (fun p : A × B => c p • minimalElementary p.1 p.2)
  rw [he]
  simpa only [dist_eq_norm] using hzy

end WeakPureInfiniteness

end

end OAI
