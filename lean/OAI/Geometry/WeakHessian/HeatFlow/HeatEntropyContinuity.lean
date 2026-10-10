import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatEVI
import OAI.Geometry.WeakHessian.Entropy.EntropyStability

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile66
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

omit [CompleteSpace X] in
lemma CurvatureDimension.cheegerHeat_entropy_continuousOn_weighted {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hN : 1 < N) (hfull : FullSupport m)
    (hfin : FiniteOnBoundedSets m) (o : X) (h : QuadraticCheegerEnergy m)
    (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    (μ : ℝ → ProbabilityMeasure X)
    (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    {b : ℝ} : ContinuousOn (fun t => entropyReal m (μ t:Measure X)) (Icc 0 b) := by
  have hUt (t : ℝ) (ht : 0 ≤ t) := (hcd.cheegerHeat_weighted hfin o h u hV hU ht).1
  have hn (t : ℝ) (ht : 0 ≤ t) := cheegerHeat_nonneg h ht u hun
  have hit (t : ℝ) (ht : 0 ≤ t) := (cheegerHeat_integrable hfin o h u hi ht).1
  have he (t : ℝ) (ht : 0 ≤ t) : entropyReal m (μ t:Measure X) = (∫ x,reducedEntropy (cheegerHeat h t u x) ∂m)+1 :=
    entropyReal_eq_reducedDensity _ (hn t ht) (hit t ht)
      (integrable_reducedEntropy (Lp.memLp _) (hn t ht) (weighted_pairing (hUt t ht) hD).1 hw) (μ t) (hμ t ht)
  have hc : Continuous (fun t : Icc (0:ℝ) b => cheegerHeat h t u) :=
    continuousOn_iff_continuous_domRestrict.mp ((cheegerHeat_continuousOn hfin h u).mono Icc_subset_Ici_self)
  have hnorm (t : Icc (0:ℝ) b) : ‖(hUt t t.property.1).toLp _‖ ≤ ‖hU.toLp _‖*Real.exp ((L:ℝ)^2*b) :=
    (hcd.cheegerHeat_weighted_norm hfin o h u hV hU t.property.1).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.property.2 (sq_nonneg _))) (norm_nonneg _))
  rw [continuousOn_iff_continuous_domRestrict,continuous_iff_seqContinuous]
  intro ts t hts
  change Tendsto (fun n => entropyReal m (μ (ts n):Measure X)) atTop (𝓝 (entropyReal m (μ t:Measure X)))
  simp_rw [he _ (ts _).property.1,he _ t.property.1]
  apply Tendsto.add_const
  exact integral_reducedEntropy_tendsto_weighted hhalf hhalfi ((hc.tendsto t).comp hts)
    (hn t t.property.1) (fun n => hn (ts n) (ts n).property.1)
    (hit t t.property.1) (fun n => hit (ts n) (ts n).property.1)
    (fun n => by rw [(hcd.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hi (ts n).property.1).2,
      (hcd.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hi t.property.1).2])
    (hUt t t.property.1) (fun n => hUt (ts n) (ts n).property.1) (hnorm t) (fun n => hnorm (ts n))
end WeakHessian

end
end InlinedFile66

end OAI
