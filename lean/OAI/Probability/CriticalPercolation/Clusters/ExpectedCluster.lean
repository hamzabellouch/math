import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import OAI.Probability.CriticalPercolation.ProductMeasure.Density

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma finite_spatialMarkov (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S U : Set V) (F : Set V → SimpleGraph V → ℝ) :
    expect w (fun ω =>
      F (roots (delete (G.openGraph ω) U) S)
        (delete (G.openGraph ω) (roots (delete (G.openGraph ω) U) S))) =
    expect w (fun ω => expect w (fun ω' =>
      F (roots (delete (G.openGraph ω) U) S)
        (delete (G.openGraph ω') (roots (delete (G.openGraph ω) U) S)))) := by
  classical
  refine expect_exposure w hw
    (fun ω => roots (delete (G.openGraph ω) U) S) G.incidentEdges
    (G.dependsOn_exact_deleted_roots S U)
    (fun W ω => F W (delete (G.openGraph ω) W)) ?_
  intro W ω ω' hω
  exact congrArg (F W) (G.delete_openGraph_dependsOn W hω)

noncomputable def expectedCluster (w : E → Prop → ℝ) (s : V)
    (F : Set V → ℝ) (W : Set V) : ℝ :=
  expect w (fun ω => F (component (delete (G.openGraph ω) W) s))

noncomputable def expectedResidual (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) : ℝ := by
  classical
  exact expect w (fun ω =>
    if s ∉ roots (delete (G.openGraph ω) U) S then
      G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S) -
      G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S ∪ U)
    else 0)

lemma expectedResidual_eq (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) (U : Set V) :
    G.expectedResidual w S s F U =
      expect w (fun ω => residual (G.openGraph ω) S s F U) := by
  classical
  have h := G.finite_spatialMarkov w hw S U
    (fun W H => if s ∉ W then F (component H s) - F (component (delete H U) s) else 0)
  have hu : ∀ H W, delete (delete H W) U = delete H (W ∪ U) := by
    intro H W
    rw [delete_delete, Set.union_comm]
  simp_rw [hu] at h
  change _ = expect w (fun ω => if s ∉ roots (delete (G.openGraph ω) U) S then
    F (component (delete (G.openGraph ω) (roots (delete (G.openGraph ω) U) S)) s) -
    F (component (delete (G.openGraph ω) (roots (delete (G.openGraph ω) U) S ∪ U)) s)
    else 0)
  rw [h]
  unfold expectedResidual
  congr 1
  funext ω
  split_ifs
  · rw [expect_const w hw]
  · rw [expect_sub]
    rfl

lemma expectedResidual_nonneg (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : Monotone F) (U : Set V) :
    0 ≤ G.expectedResidual w S s F U := by
  rw [expectedResidual_eq G w hw, ← expect_const w hw 0]
  exact expect_mono hpos fun ω => residual_nonneg (G.openGraph ω) S s hF U

lemma expectedResidual_monotone (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : Monotone F) :
    Monotone (G.expectedResidual w S s F) := by
  intro U U' hUU'
  rw [expectedResidual_eq G w hw, expectedResidual_eq G w hw]
  exact expect_mono hpos fun ω => residual_monotone (G.openGraph ω) S s hF hUU'

end CriticalPercolation.BondGraph

open scoped BigOperators

end
end

end OAI
