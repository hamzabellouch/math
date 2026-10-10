import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatCost
import OAI.Geometry.WeakHessian.LocalBounds.WeightedTV

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile54
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma weighted_abs_sub_memLp {u v V : X → ℝ}
    (hu : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hv : MemLp (fun x => v x*Real.exp (V x)) 2 m) :
    MemLp (fun x => |u x-v x| * Real.exp (V x)) 2 m := by
  apply MemLp.ae_eq (hf_Lp := (hu.sub hv).norm)
  exact ae_of_all _ fun x => by
    simp only [Pi.sub_apply,Real.norm_eq_abs,← sub_mul,abs_mul,abs_of_pos (Real.exp_pos _)]

lemma CurvatureDimension.cost_variation_density {K N : ℝ} (hcd : CurvatureDimension m K N)
    (o : X) (T : ℝ≥0) (u v : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    (hui : Integrable u m) (hvi : Integrable v m)
    (μ ξ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = densityMeasure m u)
    (hξ : (ξ:Measure X) = densityMeasure m v)
    (hn : (ν:Measure X) ≪ m) (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {V : X → ℝ} (hVm : Measurable V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hV : MemLp (fun x => v x*Real.exp (V x)) 2 m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m) :
    |quadraticWassersteinSq (μ:Measure X) (ν:Measure X)-quadraticWassersteinSq (ξ:Measure X) (ν:Measure X)| ≤
      2*(∫ x,|u x-v x| * (dist x o+T)^2 ∂m) := by
  have one (u v : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
      (hui : Integrable u m) (hvi : Integrable v m)
      (μ ξ : ProbabilityMeasure X) (hμ : (μ:Measure X) = densityMeasure m u)
      (hξ : (ξ:Measure X) = densityMeasure m v)
      (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
      (hV : MemLp (fun x => v x*Real.exp (V x)) 2 m) :
      quadraticWassersteinSq (μ:Measure X) (ν:Measure X)-quadraticWassersteinSq (ξ:Measure X) (ν:Measure X) ≤
        2*(∫ x,|u x-v x| * (dist x o+T)^2 ∂m) := by
    obtain ⟨q,φ,hqp,hqo,hqt,hφ,hφ0,hvar⟩ := hcd.density_cost_support o T u hun hui μ ν hμ hn hsν hU hW
    obtain ⟨q',ψ,hq'p,hq'o,hq't,_⟩ := hcd.density_cost_support o T v hvn hvi ξ ν hξ hn hsν hV hW
    have hvW : Integrable (fun x => (dist x o+T)^2) (ξ:Measure X) := by
      rw [hξ]; exact densityMeasure_quadratic_integrable o T v hvn hV hW
    have H := hvar ξ hvW q' hq'o.1 hq't
    rw [← hqo.quadraticWassersteinSq_eq,← hq'o.quadraticWassersteinSq_eq,hμ,hξ,
      integral_densityMeasure m _ hun,integral_densityMeasure m _ hvn] at H
    rw [← hμ,← hξ] at H
    have hφW := hφ.weighted_memLp o T.coe_nonneg hφ0 hVm hW
    have hprod := (weighted_pairing (weighted_abs_sub_memLp hU hV) hW).1
    have hiu := (weighted_pairing hU hφW).1
    have hiv := (weighted_pairing hV hφW).1
    have H' : (∫ x,u x*φ x ∂m)-(∫ x,v x*φ x ∂m) ≤
        ∫ x,|u x-v x| * (dist x o+T)^2 ∂m := by
      rw [← integral_sub hiu hiv]
      apply integral_mono_ae (hiu.sub hiv) hprod
      exact ae_of_all _ fun x => by
        simp only [Pi.sub_apply,← sub_mul]
        calc
          _ ≤ |(u x-v x)*φ x| := le_abs_self _
          _ = |u x-v x| * |φ x| := abs_mul _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left (hφ.centered_bound T.coe_nonneg hφ0 x) (abs_nonneg _)
    exact H.trans (mul_le_mul_of_nonneg_left H' (by norm_num))
  apply abs_le.mpr
  refine ⟨?_,one u v hun hvn hui hvi μ ξ hμ hξ hU hV⟩
  have H := one v u hvn hun hvi hui ξ μ hξ hμ hV hU
  simp_rw [abs_sub_comm (v _) (u _)] at H
  linarith

lemma CurvatureDimension.cost_tendsto_density {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) (o : X) (T : ℝ≥0)
    {ι : Type*} {l : Filter ι} {us : ι → Lp ℝ 2 m} {u : Lp ℝ 2 m}
    (hlim : Tendsto us l (𝓝 u)) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (husn : ∀ i,∀ᵐ x ∂m,0 ≤ us i x) (hui : Integrable u m) (husi : ∀ i,Integrable (us i) m)
    (μ : ProbabilityMeasure X) (μs : ι → ProbabilityMeasure X) (ν : ProbabilityMeasure X)
    (hμ : (μ:Measure X) = densityMeasure m u) (hμs : ∀ i,(μs i:Measure X) = densityMeasure m (us i))
    (hn : (ν:Measure X) ≪ m) (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {V : X → ℝ} (hVm : Measurable V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hUs : ∀ i,MemLp (fun x => us i x*Real.exp (V x)) 2 m)
    {B : ℝ} (hB : ∀ᶠ i in l,‖(hUs i).toLp _‖ ≤ B)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m) :
    Tendsto (fun i => quadraticWassersteinSq (μs i:Measure X) (ν:Measure X)) l
      (𝓝 (quadraticWassersteinSq (μ:Measure X) (ν:Measure X))) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfin _ Metric.isBounded_ball⟩⟩
  have hcut (n : ℕ) : MemLp (fun x => (dist x o+T)^2*radialCutoff o n x) 2 m :=
    ((by fun_prop : Continuous (fun x => (dist x o+T)^2)).mul (radialCutoff_lipschitz o n).continuous).memLp_of_hasCompactSupport
      ((radialCutoff_compact o n).mul_left)
  have H : Tendsto (fun i => 2*(∫ x,|us i x-u x| * (dist x o+T)^2 ∂m)) l (𝓝 0) := by
    simpa only [mul_zero] using (weighted_absolute_tendsto hW o hcut hlim hU hUs hB).const_mul 2
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [H.eventually_lt_const hε] with i hi
  simp only [dist_eq_norm,Real.norm_eq_abs]
  exact (hcd.cost_variation_density o T (us i) u (husn i) hun (husi i) hui (μs i) μ ν (hμs i) hμ hn hsν
    hVm (hUs i) hU hW).trans_lt hi
end WeakHessian

end
end InlinedFile54

end OAI
