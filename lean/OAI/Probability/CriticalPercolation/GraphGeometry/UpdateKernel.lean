import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ExpectedCluster
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteMarkovAvg
import OAI.Probability.CriticalPercolation.Clusters.ClusterUpdate
import OAI.Probability.CriticalPercolation.Clusters.DeleteBot
import OAI.Probability.CriticalPercolation.ProductMeasure.DensityMulExpect

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

noncomputable def updateKernel (w : E → Prop → ℝ) (S : Set V) (s : V)
    (U Z : Set V) : ℝ :=
  G.clusterUpdate w S s (fun Y => if Y = Z then 1 else 0) U

lemma clusterUpdate_eq_sum (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) :
    G.clusterUpdate w S s F U = ∑ Z, G.updateKernel w S s U Z * F Z := by
  classical
  unfold updateKernel clusterUpdate expectedCluster
  simp_rw [← expect_mul_const, ← expect_sum]
  congr 1
  funext ω
  congr 1
  funext ω'
  simp

omit [Fintype V] in
lemma updateKernel_nonneg (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) (U Z : Set V) : 0 ≤ G.updateKernel w S s U Z :=
  G.clusterUpdate_nonneg w hpos S s (fun _ => by split_ifs <;> norm_num) U

lemma updateKernel_mass (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (U : Set V) : ∑ Z, G.updateKernel w S s U Z = 1 := by
  have h := G.clusterUpdate_eq_sum w S s (fun _ => 1) U
  simpa only [clusterUpdate, expectedCluster, expect_const w hw, mul_one] using h.symm

omit [Fintype V] in
lemma allClosed_weight_le_kernel (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hpos : ∀ e b, 0 ≤ w e b) (S : Set V) (s : V) (U : Set V) :
    density w (fun _ => False) ≤ G.updateKernel w S s U {s} := by
  unfold updateKernel clusterUpdate expectedCluster
  rw [← expect_const w hw (density w (fun _ => False))]
  apply expect_mono hpos
  intro ω
  have h := density_mul_le_expect hpos
    (f := fun ω' => if component (delete (G.openGraph ω')
      (roots (delete (G.openGraph ω) U) S)) s = {s} then 1 else 0)
    (fun _ => by split_ifs <;> norm_num) (fun _ => False)
  simpa only [show (fun _ : E => False) = (∅ : Set E) from rfl,
    G.openGraph_empty, delete_bot, component_bot, ite_true, mul_one] using h

lemma avoidedAverage_eq_sum (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) :
    G.avoidedAverage w S s F = ∑ U,
      G.avoidedAverage w S s (fun Z => if Z = U then 1 else 0) * F U := by
  classical
  unfold avoidedAverage
  simp_rw [← expect_mul_const, ← expect_sum]
  congr 1
  funext ω
  split_ifs <;> simp_all

noncomputable def avoidedLaw (w : E → Prop → ℝ) (S : Set V) (s : V) (U : Set V) : ℝ :=
  G.avoidedAverage w S s (fun Z => if Z = U then 1 else 0) /
    G.avoidedAverage w S s (fun _ => 1)

lemma avoidedLaw_avg (w : E → Prop → ℝ) (S : Set V) (s : V) (F : Set V → ℝ) :
    FiniteMarkov.avg (G.avoidedLaw w S s) F =
      G.avoidedAverage w S s F / G.avoidedAverage w S s (fun _ => 1) := by
  classical
  unfold FiniteMarkov.avg avoidedLaw
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [← G.avoidedAverage_eq_sum]

omit [Fintype V] in
lemma avoidedLaw_nonneg (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) (U : Set V) : 0 ≤ G.avoidedLaw w S s U := by
  unfold avoidedLaw avoidedAverage
  apply div_nonneg <;> apply expect_nonneg hpos <;> intro ω <;> positivity

omit [Fintype V] in
lemma allClosed_weight_le_avoidance (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) (hs : s ∉ S) :
    density w (fun _ => False) ≤ G.avoidedAverage w S s (fun _ => 1) := by
  unfold avoidedAverage
  have h := density_mul_le_expect hpos
    (f := fun ω => if s ∉ roots (G.openGraph ω) S then (1 : ℝ) else 0)
    (fun _ => by split_ifs <;> norm_num) (fun _ => False)
  simpa only [show (fun _ : E => False) = (∅ : Set E) from rfl,
    G.openGraph_empty, roots_bot, ite_eq_left hs, mul_one] using h

omit [Fintype V] in
lemma avoidance_pos (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (S : Set V) (s : V) (hs : s ∉ S) :
    0 < G.avoidedAverage w S s (fun _ => 1) := by
  have hp : 0 < density w (fun _ => False) := Finset.prod_pos fun e _ => hclosed e
  exact hp.trans_le (G.allClosed_weight_le_avoidance w hpos S s hs)

lemma avoidedLaw_mass (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (S : Set V) (s : V) (hs : s ∉ S) :
    ∑ U, G.avoidedLaw w S s U = 1 := by
  have h := G.avoidedLaw_avg w S s (fun _ => 1)
  simpa only [FiniteMarkov.avg, mul_one, div_self (ne_of_gt (G.avoidance_pos w hpos hclosed S s hs))]
    using h

lemma avoidedLaw_stationary (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (Z : Set V) :
    ∑ U, G.avoidedLaw w S s U * G.updateKernel w S s U Z = G.avoidedLaw w S s Z := by
  change FiniteMarkov.avg (G.avoidedLaw w S s)
    (G.clusterUpdate w S s (fun Y => if Y = Z then 1 else 0)) = _
  rw [G.avoidedLaw_avg, G.clusterUpdate_stationary w hw]
  rfl

lemma tendsto_clusterUpdate (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (S : Set V) (s : V) (hs : s ∉ S) (F : Set V → ℝ) (U : Set V) :
    Filter.Tendsto (fun n => (G.clusterUpdate w S s)^[n] F U) Filter.atTop
      (nhds (G.avoidedAverage w S s F / G.avoidedAverage w S s (fun _ => 1))) := by
  have hstep : G.clusterUpdate w S s = FiniteMarkov.step (G.updateKernel w S s) := by
    funext f Z
    exact G.clusterUpdate_eq_sum w S s f Z
  have ha : 0 < density w (fun _ => False) := Finset.prod_pos fun e _ => hclosed e
  have haone : density w (fun _ => False) ≤ 1 := by
    have h := density_mul_le_expect hpos (f := fun _ => 1) (fun _ => by norm_num)
      (fun _ => False)
    simpa only [mul_one, expect_const w hw] using h
  rw [hstep, ← G.avoidedLaw_avg]
  exact FiniteMarkov.tendsto_iterate (G.updateKernel_nonneg w hpos S s)
    (G.updateKernel_mass w hw S s) ha haone
    (G.allClosed_weight_le_kernel w hw hpos S s) _ (G.avoidedLaw_nonneg w hpos S s)
    (G.avoidedLaw_mass w hpos hclosed S s hs) (G.avoidedLaw_stationary w hw S s) F U

end CriticalPercolation.BondGraph

end
end

end OAI
