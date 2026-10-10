import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.SpatialHeat
import OAI.Geometry.WeakHessian.LocalBounds.WeightedCZero

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile115
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.cheegerHeat_compactDatum_CZero {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hfc : HasCompactSupport f) (hf2 : MemLp f 2 m)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ g : X → ℝ,LipschitzWith (L*⟨Real.exp (-K*t),(Real.exp_pos _).le⟩) g ∧
      g =ᵐ[m] cheegerHeat h t (hf2.toLp f) ∧
      ∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ x : X,R < dist x o → |g x| < ε := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  obtain ⟨B,hB⟩ := hfc.isCompact_range hf.continuous |>.isBounded.exists_norm_le
  obtain ⟨g,hg,hge⟩ := hrcd.cheegerHeat_lipschitzVersion hN hfull hfin h hf hf2
    (fun x => by simpa only [Real.norm_eq_abs] using hB (f x) ⟨x,rfl⟩) ht
  refine ⟨g,hg,hge,hrcd.1.lipschitz_vanishes_of_expWeighted hN hfull hfin o hg ?_⟩
  intro a ha
  have hV := lipschitz_mul_dist o a
  have hWf : MemLp (fun x => f x*Real.exp (a*dist x o)) 2 m :=
    (hf.continuous.mul (Real.continuous_exp.comp hV.continuous)).memLp_of_hasCompactSupport hfc.mul_right
  have hWu : MemLp (fun x => hf2.toLp f x*Real.exp (a*dist x o)) 2 m :=
    (memLp_congr_ae (hf2.coeFn_toLp.mul (Filter.EventuallyEq.rfl)).symm).mp hWf
  have H := (hrcd.1.cheegerHeat_weighted hfin o h (hf2.toLp f) hV hWu ht).1
  exact (memLp_congr_ae (hge.mul Filter.EventuallyEq.rfl).symm).mp H
end WeakHessian

end
end InlinedFile115

end OAI
