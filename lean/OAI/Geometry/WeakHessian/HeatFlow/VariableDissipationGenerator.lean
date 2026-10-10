import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.ResolventGraphConvergence
import OAI.Geometry.WeakHessian.LocalBounds.VariableDissipationTest
import OAI.Geometry.WeakHessian.LocalBounds.VariableDuhamelClosure

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_variable_generator {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    {Cf Cξ : ℝ} (hCf : 0 ≤ Cf)
    (hCξ : 0 ≤ Cξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|f x| ≤ Cf)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T : ℝ} (hT : 0 ≤ T) :
    HeatVariableDissipation h (fun x => K-a*G x) f ξ T := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hVB
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal) hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let : IsLocallyFiniteMeasure ν := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hnfin _ Metric.isBounded_ball⟩⟩
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp (|a| *CF)).toNNReal) (D := (Real.exp (|a| *CF)).toNNReal) hm hν
  let ts : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hts (n : ℕ) : 0 < ts n := by dsimp [ts]; positivity
  have ht0 : Tendsto ts atTop (𝓝 0) := by
    simpa only [ts,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let R := fun n => (Q.scale (hts n)).resolventLinear
  choose vs As AAs he hg hAg hvb hAb hAAb using
    (fun n => cheeger_double_resolvent_core h (hts n) hCf f hfb)
  have hRgraph := cheeger_double_resolvent_graph_tendsto h hf hts ht0
  have hAs (n : ℕ) : As n = R n (R n Af) := by
    apply Q.formGenerator_unique (cheeger_domain_dense h) (hg n)
    rw [he n]
    exact hRgraph.1 n
  have hvs : Tendsto vs atTop (𝓝 f) := hRgraph.2.1.congr (fun n => (he n).symm)
  have hAslim : Tendsto As atTop (𝓝 Af) := hRgraph.2.2.congr (fun n => (hAs n).symm)
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  have hfS : Sobolev ν (f : X → ℝ) := (identified_sobolev_iff_energy hnfin hID).mpr hf.1
  have hvS (n : ℕ) : Sobolev ν (vs n : X → ℝ) := (identified_sobolev_iff_energy hnfin hID).mpr (hg n).1
  obtain ⟨hE,M,hM⟩ := Q.graph_energy_limits hg hf hvs hAslim
  have hkm : AEStronglyMeasurable (fun x => K-a*G x) ν :=
    (continuous_const.sub (continuous_const.mul hGc)).aestronglyMeasurable
  have hCG : 0 ≤ CG := (abs_nonneg (G o)).trans (hGb o)
  have hkb : ∀ᵐ x ∂ν, |K-a*G x| ≤ |K|+|a| *CG := ae_of_all _ fun x =>
    (abs_sub _ _).trans (by rw [abs_mul]; gcongr; exact hGb x)
  apply heatVariableDissipation_of_energy_tendsto hnfin hID h hvS hfS hE hM hCξ hξb hkm
    (by positivity : 0 ≤ |K|+|a| *CG) hkb hT
  intro n
  constructor
  · have hc := hrcd.weighted_heat_curvature_continuousOn hN hfull hfin o hV hVB h ξ
      (hg n) hCf (by positivity) (hvb n) (hAb n) hkm hkb T
    exact (hc.mono (by rw [uIcc_of_le hT])).intervalIntegrable
  · exact hHess.rcd_weighted_heat_variable_bounded_test hN hrcd hfull hfin o hF hFb hGb hGc ha h
      (hg n) (hAg n) hCf (by positivity) (by positivity) hCξ
      (hvb n) (hAb n) (hAAb n) hξb hξ0 hT
end WeakHessian

end
end

end OAI
