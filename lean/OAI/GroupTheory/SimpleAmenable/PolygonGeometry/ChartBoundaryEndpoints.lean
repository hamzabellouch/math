import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.OpenAffineCharts

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ChartBoundaryEndpoints
open Classical Set

def squareBoundaryCuts : Finset PlaneCut := {(0,0),(0,1),(1,0),(1,1)}

theorem interval_endpoints_closed {X : Type*} [TopologicalSpace X] {f : ℝ → X}
    (hf : Continuous f) {A : Set X} (hA : IsClosed A) {L U : ℝ} (hLU : L < U)
    (h : ∀r ∈ Ioo L U,f r ∈ A) : f L ∈ A ∧ f U ∈ A := by
  have hs : closure (Ioo L U) ⊆ f ⁻¹' A := (hA.preimage hf).closure_subset_iff.mpr h
  rw [closure_Ioo hLU.ne] at hs
  exact ⟨hs (left_mem_Icc.mpr hLU.le),hs (right_mem_Icc.mpr hLU.le)⟩

theorem squareBoundaryCuts_of_closed_not_open {a : ℕ} {p : ℝ×ℝ}
    (hp : p ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) (hn : p ∉ squareInterior) :
    ∃l ∈ squareBoundaryCuts,cutForm a l.1 p=ordinary l.2 := by
  by_cases hx₀ : p.1=0
  · exact ⟨(0,0),by simp [squareBoundaryCuts],by simp [cutForm,hx₀]⟩
  by_cases hx₁ : p.1=1
  · exact ⟨(0,1),by simp [squareBoundaryCuts],by simp [cutForm,hx₁]⟩
  by_cases hy₀ : p.2=0
  · exact ⟨(1,0),by simp [squareBoundaryCuts],by simp [cutForm,hy₀]⟩
  by_cases hy₁ : p.2=1
  · exact ⟨(1,1),by simp [squareBoundaryCuts],by simp [cutForm,hy₁]⟩
  exact False.elim (hn ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm hx₀),lt_of_le_of_ne hp.1.2 hx₁⟩,
    ⟨lt_of_le_of_ne hp.2.1 (Ne.symm hy₀),lt_of_le_of_ne hp.2.2 hy₁⟩⟩)

theorem squareBoundaryCuts_nonzero_on_interior {a : ℕ} {p : ℝ×ℝ}
    (hp : p ∈ squareInterior) {l : PlaneCut} (hl : l ∈ squareBoundaryCuts) :
    cutForm a l.1 p ≠ ordinary l.2 := by
  simp only [squareBoundaryCuts,Finset.mem_insert,Finset.mem_singleton] at hl
  rcases hl with rfl|rfl|rfl|rfl
  · simpa [cutForm] using ne_of_gt hp.1.1
  · simpa [cutForm] using ne_of_lt hp.1.2
  · simpa [cutForm] using ne_of_gt hp.2.1
  · simpa [cutForm] using ne_of_lt hp.2.2

theorem barrier_geometric_endpoint_cut {a : ℕ} {j : Fin 4} {c : CutRing} {N r : ℝ}
    (hc : c ∈ barrierCandidate a j N)
    (hr : r=barrierLineLower a j c ∨ r=barrierLineUpper a j c) :
    ∃l ∈ squareBoundaryCuts,j ≠ l.1 ∧ cutForm a l.1 (barrierLinePoint a j c r)=ordinary l.2 := by
  have hgap := barrierLineLower_lt_upper hc
  have hh := interval_endpoints_closed (barrierLinePoint_continuous a j c)
    (isClosed_Icc.prod isClosed_Icc) hgap
    (fun t ht => let hp := (barrierLinePoint_interior_iff hc t).mpr ht
      show barrierLinePoint a j c t ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 from
        ⟨⟨hp.1.1.le,hp.1.2.le⟩,⟨hp.2.1.le,hp.2.2.le⟩⟩)
  have hclosed : barrierLinePoint a j c r ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 :=
    hr.elim (fun h => h ▸ hh.1) (fun h => h ▸ hh.2)
  have hn : barrierLinePoint a j c r ∉ squareInterior := by
    rw [barrierLinePoint_interior_iff hc r]
    rcases hr with rfl|rfl <;> simp
  obtain ⟨l,hl,hcut⟩ := squareBoundaryCuts_of_closed_not_open hclosed hn
  refine ⟨l,hl,?_,hcut⟩
  intro he
  obtain ⟨p,hp,hpc⟩ := hc.2
  have hjc := cutForm_barrierLinePoint a j c r
  rw [←he] at hcut
  have hp' := hpc.trans (hjc.symm.trans hcut)
  rw [he] at hp'
  exact squareBoundaryCuts_nonzero_on_interior hp hl hp'

theorem chart_line_endpoints_forced {a : ℕ} (T : Finset PlaneCut) (p : GenericSquare a)
    {j : Fin 4} {c : CutRing} {N x : ℝ} (hc : c ∈ barrierCandidate a j N)
    (hx : barrierLinePoint a j c x ∈ openSquareChart T p) :
    ∃L U : ℝ,x ∈ Ioo L U ∧
      L ∈ Icc (barrierLineLower a j c) (barrierLineUpper a j c) ∧
      U ∈ Icc (barrierLineLower a j c) (barrierLineUpper a j c) ∧
      (∀r ∈ Ioo L U,barrierLinePoint a j c r ∈ openSquareChart T p) ∧
      (∀r ∈ ({L,U} : Finset ℝ),∃l ∈ T ∪ squareBoundaryCuts,j ≠ l.1 ∧
        cutForm a l.1 (barrierLinePoint a j c r)=ordinary l.2) := by
  obtain ⟨L,U,hx,hL,hU,hchart,hend⟩ := openSquareChart_line_interval T p hc hx
  refine ⟨L,U,hx,hL,hU,hchart,?_⟩
  intro r hr
  rcases hend r hr with h | h | h
  · obtain ⟨l,hl,hj,hc⟩ := barrier_geometric_endpoint_cut hc (Or.inl h)
    exact ⟨l,Finset.mem_union_right _ hl,hj,hc⟩
  · obtain ⟨l,hl,hj,hc⟩ := barrier_geometric_endpoint_cut hc (Or.inr h)
    exact ⟨l,Finset.mem_union_right _ hl,hj,hc⟩
  · obtain ⟨l,hl,hj,hc⟩ := h
    exact ⟨l,Finset.mem_union_left _ hl,hj,hc⟩

end ChartBoundaryEndpoints

end SimpleAmenable
end
end

end OAI
