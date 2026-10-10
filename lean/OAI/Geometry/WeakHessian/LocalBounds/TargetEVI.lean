import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.RadialCost
import OAI.Geometry.WeakHessian.HeatFlow.HeatEntropyContinuity
import OAI.Geometry.WeakHessian.LocalBounds.WeightedEVI

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile68
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma intervalIntegral_exp_entropy_tendsto {K b : ℝ} (hb : 0 ≤ b) {E : ℝ → ℝ}
    (hE : ContinuousOn E (Icc 0 b)) {ι : Type*} {l : Filter ι} {c : ι → ℝ} {c0 : ℝ}
    (hc : Tendsto c l (𝓝 c0)) :
    Tendsto (fun i => ∫ t in 0..b,Real.exp (K*t)*(c i-E t)) l
      (𝓝 (∫ t in 0..b,Real.exp (K*t)*(c0-E t))) := by
  have heI : IntervalIntegrable (fun t : ℝ => Real.exp (K*t)) volume 0 b := (by fun_prop : Continuous (fun t : ℝ => Real.exp (K*t))).intervalIntegrable _ _
  have hEI : IntervalIntegrable (fun t : ℝ => Real.exp (K*t)*E t) volume 0 b :=
    ((by fun_prop : ContinuousOn (fun t : ℝ => Real.exp (K*t)) (Icc 0 b)).mul hE).intervalIntegrable_of_Icc hb
  have heq (z : ℝ) : (∫ t in 0..b,Real.exp (K*t)*(z-E t)) =
      z*(∫ t in 0..b,Real.exp (K*t))-(∫ t in 0..b,Real.exp (K*t)*E t) := by
    have hf : (fun t : ℝ => Real.exp (K*t)*(z-E t)) = fun t => z*Real.exp (K*t)-Real.exp (K*t)*E t := by funext t; ring
    rw [hf,intervalIntegral.integral_sub (heI.const_mul z) hEI,intervalIntegral.integral_const_mul]
  simp_rw [heq]
  exact (hc.mul_const _).sub_const _

lemma RCD.cheegerHeat_comparison_weighted_target {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hmass : ∫ x,u x ∂m = 1)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,|u x| ≤ B)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hdecayi : Integrable (fun x => Real.exp (-V x)) m)
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    (hW : ∀ T : ℝ≥0, MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m ∧
      MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (ν : ProbabilityMeasure X) (w : X → ℝ) (hw : MemLp w 2 m) (hwm : Measurable w)
    (hν : (ν:Measure X) = squareDensityMeasure m w)
    (hνE : FiniteEntropy m (ν:Measure X))
    (hνM : Integrable (fun x => dist x o^2) (ν:Measure X))
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m)
    {b : ℝ} (hb : 0 ≤ b) :
    (Real.exp (K*b)*quadraticWassersteinSq (μ b:Measure X) (ν:Measure X)-
      quadraticWassersteinSq (μ 0:Measure X) (ν:Measure X))/2 ≤
      ∫ t in 0..b,Real.exp (K*t)*(entropyReal m (ν:Measure X)-entropyReal m (μ t:Measure X)) := by
  have hUt (t : ℝ) (ht : 0 ≤ t) := (hrcd.1.cheegerHeat_weighted hfin o h u hV hU ht).1
  have hμM (t : ℝ) (ht : 0 ≤ t) : Integrable (fun x => dist x o^2) (μ t:Measure X) := by
    rw [hμ t ht]
    simpa only [NNReal.coe_zero,add_zero] using densityMeasure_quadratic_integrable o 0 (cheegerHeat h t u)
      (cheegerHeat_nonneg h ht u hun) (hUt t ht) (hW 0).1
  have hEc := hrcd.1.cheegerHeat_entropy_continuousOn_weighted hN hfull hfin o h u hun
    (integrable_of_integral_eq_one hmass) hV hU hD hdecayi hhalf hhalfi μ hμ (b := b)
  let : IsProbabilityMeasure (squareDensityMeasure m w) := hν ▸ inferInstance
  obtain ⟨k,c,hc,hcT,hp⟩ := radial_probability_normalization hw hwm o
  let νs (n : ℕ) : ProbabilityMeasure X := squareDensityProbability m (fun x => c n*(w x*radialCutoff o (n+k) x)) (hp n)
  have hνs (n : ℕ) : (νs n:Measure X) = squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x)) := rfl
  have hMC := normalized_radial_cost_tendsto hwm ν hν o k (fun n => (hc n).1) hcT νs hνs hνM
  have hET := normalized_radial_entropy_tendsto hw hwm (hν ▸ hνE) o k
    (fun n => ⟨(hc n).1.le,(hc n).2⟩) hcT hp
  have hET' : Tendsto (fun n => entropyReal m (νs n:Measure X)) atTop (𝓝 (entropyReal m (ν:Measure X))) := by
    simpa only [hνs,hν] using hET.2
  have hcost (t : ℝ) (ht : 0 ≤ t) := quadraticWassersteinSq_tendsto_of_cost_zero (μ t) ν νs o (hμM t ht) hνM hMC.1 hMC.2
  have hleft := (((hcost b hb).const_mul (Real.exp (K*b))).sub (hcost 0 le_rfl)).div_const 2
  have hright := intervalIntegral_exp_entropy_tendsto hb hEc (K := K) hET'
  apply le_of_tendsto_of_tendsto' hleft hright
  intro n
  let T : ℝ≥0 := (n+k:ℕ)+1
  have hT : 0 < T := by dsimp [T]; positivity
  have hsν : (νs n:Measure X) (Metric.closedBall o T)ᶜ = 0 := by
    rw [hνs n]
    simpa only [T,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using squareDensity_normalized_radial_support hwm o (n+k) (c n)
  have hd : (νs n:Measure X) ≤ ((4:ℝ≥0∞)*C) • m := by
    rw [hνs n]
    apply (squareDensity_normalized_radial_le hwm o (n+k) (by rw [abs_of_pos (hc n).1]; exact (hc n).2)).trans
    rw [← hν,← smul_smul]
    exact _root_.smul_le_smul_left _ hdν
  exact hrcd.cheegerHeat_comparison_weighted hN hfull hfin o h u hun hmass hB huB hV hU
    hdecay hD hdecayi hhalf hhalfi μ hμ (νs n) T hT hsν
    (ENNReal.mul_ne_top (by norm_num) hCt) hd (hW T).1 (hW T).2 hb
end WeakHessian

end
end InlinedFile68

end OAI
