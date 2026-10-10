import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CheegerEnergyConst
import OAI.Geometry.WeakHessian.Sobolev.AddConst

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile105
noncomputable section
namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma ClosedQuadraticEnergy.energy_sub_tendsto_zero {Q : E → ℝ≥0∞}
    (hQ : ClosedQuadraticEnergy Q) {ι : Type*} {l : Filter ι} {f : ι → E} {u : E}
    (hu : Q u < ∞) (hf : Tendsto f l (𝓝 u)) (hb : ∀ᶠ i in l, Q (f i) ≤ Q u) :
    Tendsto (fun i => (Q (f i-u)).toReal) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsum := hf.add_const u
  let r := 4*(Q u).toReal-ε
  have h2 := hQ.add_lt_top hu hu
  have he2 : (Q (u+u)).toReal = 4*(Q u).toReal := by
    rw [show u+u = (2:ℝ) • u by simp [two_smul],hQ.smul,ENNReal.toReal_mul]
    norm_num
  have HH (i : ι) (hi : Q (f i) ≤ Q u) :
      (Q (f i+u)).toReal+(Q (f i-u)).toReal ≤ 4*(Q u).toReal := by
    have hfi := hi.trans_lt hu
    have hp := congrArg ENNReal.toReal (hQ.parallelogram (f i) u hfi hu)
    rw [ENNReal.toReal_add (hQ.add_lt_top hfi hu).ne (hQ.sub_lt_top hfi hu).ne,
      ENNReal.toReal_add (by finiteness) (by finiteness)] at hp
    simp only [ENNReal.toReal_mul,ENNReal.toReal_ofNat] at hp
    have he := ENNReal.toReal_mono hu.ne hi
    linarith
  by_cases hr : r < 0
  · filter_upwards [hb] with i hi
    rw [Real.dist_eq,sub_zero,abs_of_nonneg ENNReal.toReal_nonneg]
    have hs := ENNReal.toReal_nonneg (a := Q (f i+u))
    dsimp only [r] at hr
    linarith [HH i hi]
  · have hr0 : 0 ≤ r := le_of_not_gt hr
    have hh : ENNReal.ofReal r < Q (u+u) := by
      rw [← ENNReal.ofReal_toReal h2.ne]
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr0).mpr
      rw [he2]
      dsimp only [r]
      linarith
    have hev := hsum.eventually ((hQ.lowerSemicontinuous.lowerSemicontinuousAt (u+u)) _ hh)
    filter_upwards [hb,hev] with i hi hs
    have hfi := hi.trans_lt hu
    have hs' := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top (hQ.add_lt_top hfi hu).ne).mpr hs
    rw [ENNReal.toReal_ofReal hr0] at hs'
    rw [Real.dist_eq,sub_zero,abs_of_nonneg ENNReal.toReal_nonneg]
    dsimp only [r] at hs'
    linarith [HH i hi]
end WeakHessianFunctional

namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
lemma cheegerHeat_energy_sub_zero (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {u : Lp ℝ 2 m} (hu : cheegerEnergy m (u : X → ℝ) < ∞) :
    Tendsto (fun t => (cheegerEnergy m (cheegerHeat h t u-u : Lp ℝ 2 m)).toReal)
      (𝓝[≥] 0) (𝓝 0) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  exact (cheeger_closedQuadraticEnergy h).energy_sub_tendsto_zero hu
    (cheegerHeat_strong_zero h u) (by filter_upwards [self_mem_nhdsWithin] with t ht; exact cheegerHeat_energy_le h ht u)
end WeakHessian

end
end InlinedFile105

end OAI
