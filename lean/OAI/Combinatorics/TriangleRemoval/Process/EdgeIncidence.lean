import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.LinkStarMatrix
import OAI.Combinatorics.TriangleRemoval.Spectral.ExtendStarApply
import OAI.Combinatorics.TriangleRemoval.Process.IncidenceDegree

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave
open scoped Matrix.Norms.Operator

noncomputable def edgeIncidence {n : ℕ} (G : Graph n) : Matrix G (Fin n) ℝ :=
  fun e u => if u ∈ e.val then 1 else 0

theorem edgeIncidence_nonneg {n : ℕ} (G : Graph n) (e : G) (u : Fin n) :
    0 ≤ edgeIncidence G e u := by simp [edgeIncidence]; split_ifs <;> norm_num

theorem edgeIncidence_idem {n : ℕ} (G : Graph n) (e : G) (u : Fin n) :
    edgeIncidence G e u * edgeIncidence G e u = edgeIncidence G e u := by
  simp [edgeIncidence]

theorem edgeIncidence_row {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (e : G) :
    ∑ u, edgeIncidence G e u = 2 := by
  simp only [edgeIncidence,Finset.sum_boole]
  have hh : Finset.univ.filter (fun u => u ∈ e.val) = e.val := by ext; simp
  rw [hh,mem_completeGraph.mp (hG e.property)]
  norm_num

theorem edgeIncidence_degree {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    incidenceDegree (edgeIncidence G) u = currentDegree G u := by
  simp only [incidenceDegree,edgeIncidence,Finset.sum_boole]
  change ((edgeStar G u).card : ℝ) = _
  rw [edgeStar_card G hG u]

theorem globalStarAverage_factorization {n : ℕ} (G : Graph n)
    (hG : G ⊆ completeGraph n) :
    globalStarAverage G = edgeIncidence G * starAverage (edgeIncidence G) := by
  ext e f
  simp only [globalStarAverage,Matrix.sum_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro u _
  rw [extendStar_apply]
  simp only [starAverage,edgeIncidence_degree G hG,edgeIncidence]
  have hc : Fintype.card (edgeStar G u) = currentDegree G u := by
    simpa only [Fintype.card_coe] using edgeStar_card G hG u
  simp only [averagingProjector,hc]
  by_cases he : u ∈ e.val <;> by_cases hf : u ∈ f.val <;> simp [he,hf,one_div]

theorem graph_star_semigroup_bound {n : ℕ} [NeZero n] (G : Graph n)
    [Nonempty G] (hG : G ⊆ completeGraph n) (hdeg : ∀ u, 0 < currentDegree G u)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • globalStarAverage G)‖ ≤ 1 + 2*s := by
  rw [globalStarAverage_factorization G hG]
  apply star_semigroup_bound _ (edgeIncidence_nonneg G) (edgeIncidence_idem G)
    (edgeIncidence_row G hG) _ s hs
  intro u
  rw [edgeIncidence_degree G hG]
  exact_mod_cast hdeg u

end SharpTerminalLeave

end
end

end OAI
