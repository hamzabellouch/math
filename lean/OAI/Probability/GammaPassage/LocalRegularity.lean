import OAI.Probability.GammaPassage.LocalResamplingModel
import Mathlib.Topology.Order.Lattice
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

namespace GammaFPP.FiniteLocal
open PlanarFPP MeasureTheory

lemma pathCost_eq_of_agree (w w' : Edge → ℝ) (p : Vertex) (ds : List Step)
    (h : ∀ e ∈ (trace p ds).map traversalEdge, w e = w' e) :
    pathCost w p ds = pathCost w' p ds := by
  rw [pathCost_trace_edge_sum, pathCost_trace_edge_sum]
  congr 1
  exact List.map_congr_left h

lemma candidate_pathCost_eq (w w' : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (h : ∀ e ∈ localEdges p q R, w e = w' e)
    (ds : List Step) (hds : ds ∈ candidates p q R) :
    pathCost w p ds = pathCost w' p ds := by
  apply pathCost_eq_of_agree
  intro e he
  exact h e (candidate_edges_subset p q R ds hds (List.mem_toFinset.mpr he))

/-- Agreement on the finite local edge set implies equality of local passage times. -/
theorem passageTime_eq_of_agree (w w' : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (h : ∀ e ∈ localEdges p q R, w e = w' e) :
    passageTime w p q R = passageTime w' p q R := by
  unfold passageTime
  congr 1
  ext c
  constructor
  · rintro ⟨ds, hds, rfl⟩
    exact ⟨ds, hds, candidate_pathCost_eq w w' p q R h ds hds⟩
  · rintro ⟨ds, hds, rfl⟩
    exact ⟨ds, hds, (candidate_pathCost_eq w w' p q R h ds hds).symm⟩

/-- Restricting weights to the local edge set and extending by zero preserves
the local passage time. -/
theorem finitePassageTime_restrict (p q : Vertex) (R : ℕ) (w : Edge → ℝ) :
    finitePassageTime p q R (fun e : ↥(localEdges p q R) => w e) =
      passageTime w p q R := by
  apply passageTime_eq_of_agree
  intro e he
  exact extend_apply p q R _ ⟨e, he⟩

/-- The cost of a finite path is continuous in the edge weights. -/
lemma continuous_pathCost (p : Vertex) (ds : List Step) :
    Continuous (fun w : Edge → ℝ => pathCost w p ds) := by
  induction ds generalizing p with
  | nil => exact continuous_const
  | cons d ds ih =>
      exact (continuous_apply (d.edge p)).add (ih (p + d.delta))

/-- Identify the real sInf with the nonempty finite lattice infimum. -/
lemma passageTime_eq_inf' (w : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    passageTime w p q R =
      (candidates p q R).inf' (candidates_nonempty p q R hR)
        (fun ds => pathCost w p ds) := by
  apply le_antisymm
  · exact Finset.le_inf' (candidates_nonempty p q R hR) _
      (fun ds hds => passageTime_le_candidate w p q R ds hds)
  · obtain ⟨ds, hds, hm⟩ := minimizing_candidate w p q R hR
    rw [← hm]
    exact Finset.inf'_le _ hds

/-- Local passage time is continuous when the candidate family is nonempty. -/
theorem continuous_passageTime (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    Continuous (fun w : Edge → ℝ => passageTime w p q R) := by
  have he : (fun w : Edge → ℝ => passageTime w p q R) =
      (fun w => (candidates p q R).inf' (candidates_nonempty p q R hR)
        (fun ds => pathCost w p ds)) := by
    funext w
    exact passageTime_eq_inf' w p q R hR
  rw [he]
  exact Continuous.finset_inf'_apply (candidates_nonempty p q R hR)
    (fun ds _ => continuous_pathCost p ds)

lemma continuous_extend (p q : Vertex) (R : ℕ) : Continuous (extend p q R) := by
  classical
  apply continuous_pi
  intro e
  by_cases he : e ∈ localEdges p q R
  · simpa only [extend, dite_eq_left he] using
      (continuous_apply (⟨e, he⟩ : ↥(localEdges p q R)))
  · simpa only [extend, dite_eq_right he] using
      (continuous_const : Continuous (fun _ : Coordinates p q R => (0 : ℝ)))

@[fun_prop] theorem continuous_finitePassageTime (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) : Continuous (finitePassageTime p q R) :=
  (continuous_passageTime p q R hR).comp (continuous_extend p q R)

@[fun_prop] theorem measurable_finitePassageTime (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) : Measurable (finitePassageTime p q R) :=
  (continuous_finitePassageTime p q R hR).measurable

/-- Local passage time is measurable as a function of the edge weights. -/
@[fun_prop] theorem measurable_passageTime (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    Measurable (fun w : Edge → ℝ => passageTime w p q R) :=
  (continuous_passageTime p q R hR).measurable

end GammaFPP.FiniteLocal

end OAI
