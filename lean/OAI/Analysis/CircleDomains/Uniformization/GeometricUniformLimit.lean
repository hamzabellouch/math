import OAI.Analysis.CircleDomains.Topology.RecursiveComponentShrink
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation

namespace OAI

/-! Uniform limits from the point-independent geometric displacement
bounds used by the shrinking homeomorphisms. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_uniformLimit_of_geometric_steps
    {X Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    (f : ℕ → X → Y) (C : ℝ)
    (hstep : ∀ n x, dist (f n x) (f (n+1) x) ≤ C*componentShrinkRadius n) :
    ∃ g : X → Y, TendstoUniformly f g atTop ∧
      ∀ n x, dist (f n x) (g x) ≤ 2*C*componentShrinkRadius n := by
  have hp (x : X) : ∃ y : Y, Tendsto (fun n => f n x) atTop (𝓝 y) := by
    apply cauchySeq_tendsto_of_complete
    exact cauchySeq_of_le_geometric (1/2 : ℝ) C (by norm_num) (fun n => hstep n x)
  choose g hg using hp
  have hbound (n : ℕ) (x : X) : dist (f n x) (g x) ≤ 2*C*componentShrinkRadius n := by
    have h := dist_le_of_le_geometric_of_tendsto (1/2 : ℝ) C (by norm_num)
      (fun n => hstep n x) (hg x) n
    convert h using 1
    dsimp only [componentShrinkRadius]
    ring
  have ht : Tendsto (fun n => 2*C*componentShrinkRadius n) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)<1)).const_mul (2*C)
    simpa only [mul_zero,componentShrinkRadius] using h
  refine ⟨g,?_,hbound⟩
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  intro x
  rw [dist_comm]
  exact (hbound n x).trans_lt hn

lemma exists_continuous_uniformLimit_of_geometric_steps
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] [CompleteSpace Y]
    (f : ℕ → X → Y) (hf : ∀ n, Continuous (f n)) (C : ℝ)
    (hstep : ∀ n x, dist (f n x) (f (n+1) x) ≤ C*componentShrinkRadius n) :
    ∃ g : C(X,Y), TendstoUniformly f g atTop ∧
      ∀ n x, dist (f n x) (g x) ≤ 2*C*componentShrinkRadius n := by
  obtain ⟨g,hg,hbound⟩ := exists_uniformLimit_of_geometric_steps f C hstep
  exact ⟨⟨g,hg.continuous (Eventually.of_forall hf).frequently⟩,hg,hbound⟩

end CircleDomainRigidity

end

end OAI
