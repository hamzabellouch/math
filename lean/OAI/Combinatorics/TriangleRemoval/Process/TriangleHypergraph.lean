import Mathlib
import OAI.Combinatorics.TriangleRemoval.Coupling.HyperScanAction
import OAI.Combinatorics.TriangleRemoval.Coupling.ScanList

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave

def triangleHypergraph {n : ℕ} (G : Graph n) (T : Finset (Fin n)) : Graph n :=
  if T ∈ triangles G then T.powersetCard 2 else ∅

theorem triangleHypergraph_subset {n : ℕ} (G : Graph n) (T : Finset (Fin n)) :
    triangleHypergraph G T ⊆ G := by
  unfold triangleHypergraph
  split_ifs with hT
  · exact (mem_triangles.mp hT).2
  · exact Finset.empty_subset _

theorem triangle_hyperScanAction_eq {n : ℕ} (G E : Graph n) (hE : E ⊆ G)
    (T : Finset (Fin n)) :
    hyperScanAction (triangleHypergraph G) E T = scanAction E T := by
  by_cases hT : T ∈ triangles G
  · have hc := (mem_triangles.mp hT).1
    simp only [hyperScanAction, triangleHypergraph, hT, ite_true, scanAction,
      mem_triangles, hc, true_and]
  · have hn : T ∉ triangles E := fun ht => hT (triangles_mono hE ht)
    simp [hyperScanAction, triangleHypergraph, hT, scanAction, hn]

theorem triangle_hyperScan_eq {n : ℕ} (G E : Graph n) (hE : E ⊆ G)
    (as : List (Finset (Fin n))) :
    hyperScan (triangleHypergraph G) E as = scanList E as := by
  induction as generalizing E with
  | nil => rfl
  | cons T as ih =>
    change hyperScan (triangleHypergraph G)
      (hyperScanAction (triangleHypergraph G) E T) as = scanList (scanAction E T) as
    rw [triangle_hyperScanAction_eq G E hE T]
    exact ih _ ((scanAction_subset E T).trans hE)

theorem graph_gridQuery_eq_scan {n : ℕ} (G focus : Graph n) (hf : focus ⊆ G)
    (N : ℕ) (ω : Finset (Fin n) → Fin N) (hω : Function.Injective ω) :
    ExposureTree.evaluate ω (gridQueryDepth (triangleHypergraph G) N N N focus none) =
      decide (focus ⊆ scanList G (clockOrder (fun T => (ω T).val))) := by
  have hs := evaluate_gridQueryDepth_iff (triangleHypergraph G) N N N ω G focus none
    le_rfl hf (triangleHypergraph_subset G) (fun T h => by cases h)
  rw [timeScan_eq_hyperScan (triangleHypergraph G) (fun T => (ω T).val)
    (Fin.val_injective.comp hω) G N (fun T => (ω T).isLt),
    triangle_hyperScan_eq G G (Finset.Subset.refl G)] at hs
  apply Bool.eq_iff_iff.mpr
  simpa only [Bool.decide_iff] using hs

noncomputable def focusSurvival {n : ℕ} (G focus : Graph n) : ℝ :=
  trueProbability ((finish G).map (fun E => decide (focus ⊆ E)))

theorem graph_grid_exposure_error {n : ℕ} (G focus : Graph n) (hf : focus ⊆ G)
    (N : ℕ) [NeZero N] :
    |focusSurvival G focus - gridAnswerProbability (triangleHypergraph G) N N N focus none| ≤
      2 * (Fintype.card (Finset (Fin n)) : ℝ) ^ 2 / N +
      trueProbability ((ExposureTree.freshRecorded (gridPriorities N)
        (gridQueryDepth (triangleHypergraph G) N N N focus none) ∅).map Prod.snd) := by
  classical
  let H := triangleHypergraph G
  let p := productPMF (gridPriorities (τ := Finset (Fin n)) N)
  let b₁ := fun ω => ExposureTree.evaluate ω (gridQueryDepth H N N N focus none)
  let b₂ := fun ω : Finset (Fin n) → Fin N =>
    decide (focus ⊆ scanList G (clockOrder (fun T => (ω T).val)))
  let C : ℝ := (Fintype.card (Finset (Fin n)) : ℝ) ^ 2 / N
  have h₁ : |trueProbability (p.map b₁) - trueProbability (p.map b₂)| ≤ C := by
    apply (boolean_coupling_bound p b₁ b₂
      (fun ω => decide (¬Function.Injective ω)) ?_).trans (grid_table_ties_bound N)
    intro ω _ hω
    have hinj : Function.Injective ω := Classical.not_not.mp (of_decide_eq_false hω)
    exact graph_gridQuery_eq_scan G focus hf N ω hinj
  have h₂ : |trueProbability (p.map b₂) - focusSurvival G focus| ≤ C := by
    have hh := clock_order_error N (fun as : List (Finset (Fin n)) =>
      decide (focus ⊆ scanList G as))
    have hl := uniform_order_scan_eq_finish G Finset.univ
      (Finset.subset_univ (triangles G))
    have hh' := congrArg (fun r : PMF (Graph n) =>
      r.map (fun E => decide (focus ⊆ E))) hl
    simp only [PMF.map_comp, Function.comp_def, Finset.card_univ] at hh'
    rw [hh'] at hh
    exact hh
  have h₃ := ExposureTree.independent_exposure_error (gridPriorities N)
    (gridQueryDepth H N N N focus none)
  have h₁' : |trueProbability (p.map b₂) - trueProbability (p.map b₁)| ≤ C := by
    rw [abs_sub_comm]
    exact h₁
  have h₂' : |focusSurvival G focus - trueProbability (p.map b₂)| ≤ C := by
    rw [abs_sub_comm]
    exact h₂
  have hsum : |focusSurvival G focus - gridAnswerProbability H N N N focus none| ≤
      C + (C + trueProbability ((ExposureTree.freshRecorded (gridPriorities N)
        (gridQueryDepth H N N N focus none) ∅).map Prod.snd)) := (abs_sub_le (focusSurvival G focus) (trueProbability (p.map b₂))
    (gridAnswerProbability H N N N focus none)).trans
    (add_le_add h₂'
      ((abs_sub_le (trueProbability (p.map b₂)) (trueProbability (p.map b₁))
        (gridAnswerProbability H N N N focus none)).trans
        (add_le_add h₁' h₃)))
  convert hsum using 1; ring

end SharpTerminalLeave

open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

end

end OAI
