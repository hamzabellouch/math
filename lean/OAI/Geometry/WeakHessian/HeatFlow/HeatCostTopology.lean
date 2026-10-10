import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatAbs
import OAI.Geometry.WeakHessian.LocalBounds.CostContinuity
import OAI.Geometry.WeakHessian.LocalBounds.RadialCost
import OAI.Geometry.WeakHessian.Entropy.CostTopology

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile70
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma CurvatureDimension.cost_zero_tendsto_density {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) (o : X)
    {ι : Type*} {l : Filter ι} {us : ι → Lp ℝ 2 m} {u : Lp ℝ 2 m}
    (hlim : Tendsto us l (𝓝 u)) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (husn : ∀ i,∀ᵐ x ∂m,0 ≤ us i x) (hui : Integrable u m) (husi : ∀ i,Integrable (us i) m)
    (μ : ProbabilityMeasure X) (μs : ι → ProbabilityMeasure X)
    (hμ : (μ:Measure X) = densityMeasure m u) (hμs : ∀ i,(μs i:Measure X) = densityMeasure m (us i))
    {V : X → ℝ} (hVm : Measurable V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hUs : ∀ i,MemLp (fun x => us i x*Real.exp (V x)) 2 m)
    {B : ℝ} (hB : ∀ᶠ i in l,‖(hUs i).toLp _‖ ≤ B)
    (hW : ∀ T : ℝ≥0, MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m) :
    Tendsto (fun i => quadraticWassersteinSq (μ:Measure X) (μs i:Measure X)) l (𝓝 0) := by
  let w : X → ℝ := fun x => Real.sqrt (u x)
  have hw : MemLp w 2 m := densityMeasure_sqrt_memLp u hun hui
  have hwm : Measurable w := Lp.stronglyMeasurable u |>.measurable.sqrt
  have hroot : (μ:Measure X) = squareDensityMeasure m w := hμ.trans (densityMeasure_eq_square_sqrt u hun)
  let : IsProbabilityMeasure (squareDensityMeasure m w) := hroot ▸ inferInstance
  have hM : Integrable (fun x => dist x o^2) (μ:Measure X) := by
    rw [hμ]
    simpa only [NNReal.coe_zero,add_zero] using densityMeasure_quadratic_integrable o 0 u hun hU (hW 0)
  have hMs (i) : Integrable (fun x => dist x o^2) (μs i:Measure X) := by
    rw [hμs i]
    simpa only [NNReal.coe_zero,add_zero] using densityMeasure_quadratic_integrable o 0 (us i) (husn i) (hUs i) (hW 0)
  obtain ⟨k,c,hc,hcT,hp⟩ := radial_probability_normalization hw hwm o
  let ξ (n : ℕ) : ProbabilityMeasure X := squareDensityProbability m (fun x => c n*(w x*radialCutoff o (n+k) x)) (hp n)
  have hξ (n : ℕ) : (ξ n:Measure X) = squareDensityMeasure m (fun x => c n*(w x*radialCutoff o (n+k) x)) := rfl
  have hMC := normalized_radial_cost_tendsto hwm μ hroot o k (fun n => (hc n).1) hcT ξ hξ hM
  apply quadraticWassersteinSq_tendsto_zero_of_tests μ μs ξ o hM hMs hMC.1 hMC.2
  intro n
  let T : ℝ≥0 := (n+k:ℕ)+1
  have hsξ : (ξ n:Measure X) (Metric.closedBall o T)ᶜ = 0 := by
    rw [hξ n]
    simpa only [T,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using squareDensity_normalized_radial_support hwm o (n+k) (c n)
  have hξm : (ξ n:Measure X) ≪ m := withDensity_absolutelyContinuous _ _
  exact hcd.cost_tendsto_density hfin o T hlim hun husn hui husi μ μs (ξ n) hμ hμs hξm hsξ hVm hU hUs hB (hW T)

lemma CurvatureDimension.cheegerHeat_cost_zero_tendsto {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hui : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hW : ∀ T : ℝ≥0,MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    (μ : ℝ → ProbabilityMeasure X)
    (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    {ι : Type*} {l : Filter ι} {ts : ι → ℝ} {t : ℝ}
    (hts : ∀ i,0 ≤ ts i) (ht : 0 ≤ t) (hT : Tendsto ts l (𝓝 t)) :
    Tendsto (fun i => quadraticWassersteinSq (μ t:Measure X) (μ (ts i):Measure X)) l (𝓝 0) := by
  have hUt (s : ℝ) (hs : 0 ≤ s) := (hcd.cheegerHeat_weighted hfin o h u hV hU hs).1
  have hlim : Tendsto (fun i => cheegerHeat h (ts i) u) l (𝓝 (cheegerHeat h t u)) :=
    (cheegerHeat_continuousOn hfin h u t ht).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hT,Eventually.of_forall hts⟩)
  apply hcd.cost_zero_tendsto_density hfin o hlim (cheegerHeat_nonneg h ht u hun)
    (fun i => cheegerHeat_nonneg h (hts i) u hun) (cheegerHeat_integrable hfin o h u hui ht).1
    (fun i => (cheegerHeat_integrable hfin o h u hui (hts i)).1) (μ t) (fun i => μ (ts i))
    (hμ t ht) (fun i => hμ (ts i) (hts i)) hV.continuous.measurable (hUt t ht)
    (fun i => hUt (ts i) (hts i)) (B := ‖hU.toLp _‖*Real.exp ((L:ℝ)^2*(t+1))) _ hW
  filter_upwards [hT.eventually_le_const (by linarith : t < t+1)] with i hi
  exact (hcd.cheegerHeat_weighted_norm hfin o h u hV hU (hts i)).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hi (sq_nonneg _))) (norm_nonneg _))
end WeakHessian

end
end InlinedFile70

end OAI
