import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CompactGeneratorRange

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile172
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.original_compact_test_graph_approx {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {u A : Lp ℝ 2 m} (hu : IsLaplacian m u A) :
    ∃ gs : ℕ → X → ℝ,(∀ n,IsTestFunction m (gs n)) ∧ (∀ n,HasCompactSupport (gs n)) ∧
      ∃ us As : ℕ → Lp ℝ 2 m,(∀ n,gs n =ᵐ[m] us n) ∧
      (∀ n,laplacian m (gs n) =ᵐ[m] As n) ∧
      Tendsto us atTop (𝓝 u) ∧ Tendsto As atTop (𝓝 A) := by
  let Q := cheeger_closedQuadraticEnergy hrcd.2
  let M := compactGeneratorRange hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2)
  have hcl : u-A ∈ closure (M : Set (Lp ℝ 2 m)) := by
    change u-A ∈ M.topologicalClosure
    rw [hrcd.compactGeneratorRange_dense hN hfull hfin o]
    trivial
  obtain ⟨ys,hys,hyt⟩ := mem_closure_iff_seq_limit.mp hcl
  choose gs hgs hgsc us As hge hgA he using hys
  have hgen := hrcd.1.global_formGenerator_of_isLaplacian hfin o hrcd.2 u A hu
  have heu : Q.resolvent (u-A) = u := (Q.isFormGenerator_iff u A).mp hgen
  have heuN (n : ℕ) : Q.resolvent (ys n) = us n := by
    rw [he n]
    exact (Q.isFormGenerator_iff (us n) (As n)).mp
      (hrcd.1.global_formGenerator_of_isLaplacian hfin o hrcd.2 (us n) (As n)
        ((hgA n).congr_ae (hge n) EventuallyEq.rfl))
  have hT : Tendsto us atTop (𝓝 u) := by
    have H := Q.resolventLinear.continuous.tendsto (u-A) |>.comp hyt
    change Tendsto (fun n => Q.resolvent (ys n)) atTop (𝓝 (Q.resolvent (u-A))) at H
    simpa only [heu,heuN] using H
  refine ⟨gs,hgs,hgsc,us,As,hge,fun n => (hgA n).ae_laplacian hfin,hT,?_⟩
  have hA (n : ℕ) : As n = us n-ys n := by rw [he n]; abel
  simpa only [← hA,sub_sub_cancel] using hT.sub hyt
end WeakHessian

end
end InlinedFile172

end OAI
