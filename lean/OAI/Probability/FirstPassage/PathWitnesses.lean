import OAI.Probability.FirstPassage.Paths
import OAI.Probability.FirstPassage.WitnessDecomposition

namespace OAI

namespace PlanarFPP

abbrev Traversal := Vertex × Step

def traversalEdge (t : Traversal) : Edge := t.2.edge t.1

def trace (p : Vertex) : List Step → List Traversal
  | [] => []
  | d :: ds => (p, d) :: trace (p + d.delta) ds

noncomputable def stepDefect (τ : Edge → ℝ) (b m a : ℝ) (t : Traversal) : ℝ :=
  τ (traversalEdge t) - support b m a t.2.delta

@[simp] theorem support_zero (b m a : ℝ) : support b m a 0 = 0 := by
  simp [support, transverse]

theorem trace_total_defect (τ : Edge → ℝ) (b m a : ℝ) (p : Vertex) (ds : List Step) :
    total (stepDefect τ b m a) (trace p ds) = defect τ b m a p ds := by
  induction ds generalizing p with
  | nil => simp [trace, defect, pathCost]
  | cons d ds ih =>
    simp [trace, ih, defect, pathCost, stepDefect, traversalEdge]
    ring

theorem support_step_bound (b m a : ℝ) (d : Step) :
    support b m a d.delta ≤ max |m - a * b| |a| := by
  cases d with
  | east =>
    have he : support b m a Step.east.delta = m - a * b := by
      simp [Step.delta, support, transverse]; ring
    rw [he]
    exact (le_abs_self _).trans (le_max_left _ _)
  | west =>
    have he : support b m a Step.west.delta = -(m - a * b) := by
      simp [Step.delta, support, transverse]; ring
    rw [he]
    exact (neg_le_abs _).trans (le_max_left _ _)
  | north =>
    simpa [Step.delta, support, transverse] using (le_abs_self a).trans (le_max_right |m-a*b| |a|)
  | south =>
    simpa [Step.delta, support, transverse] using (neg_le_abs a).trans (le_max_right |m-a*b| |a|)

theorem path_witness_decomposition (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e)
    (b m a η : ℝ) (hη : 0 ≤ η) (hscale : max |m - a * b| |a| ≤ η)
    (p : Vertex) (ds : List Step)
    (hsimple : ((trace p ds).map traversalEdge).Nodup) :
    ∃ blocks : List (List Traversal), ∃ rest : List Traversal,
      trace p ds = blocks.flatten ++ rest ∧
      blocks.Pairwise (fun x y => List.Disjoint (x.map traversalEdge) (y.map traversalEdge)) ∧
      (∀ q ∈ blocks, q ≠ [] ∧
        -2 * η ≤ total (stepDefect τ b m a) q ∧ total (stepDefect τ b m a) q < -η) ∧
      -η ≤ total (stepDefect τ b m a) rest ∧
      -η - 2 * η * blocks.length ≤ defect τ b m a p ds := by
  have hstep : ∀ t ∈ trace p ds, -η ≤ stepDefect τ b m a t := by
    intro t _
    have hs := (support_step_bound b m a t.2).trans hscale
    have ht := hτ (traversalEdge t)
    unfold stepDefect
    linarith
  obtain ⟨blocks, rest, heq, hd, hb, hr, hbound⟩ :=
    edge_disjoint_witness_decomposition traversalEdge (stepDefect τ b m a) η hη
      (trace p ds) hsimple hstep
  exact ⟨blocks, rest, heq, hd, hb, hr, by simpa [trace_total_defect] using hbound⟩

end PlanarFPP

end OAI
