import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatEntropyDissipation
import OAI.Geometry.WeakHessian.Entropy.LogAddTwoSqrt
import OAI.Geometry.WeakHessian.LocalBounds.SqrtWeighted
import OAI.Geometry.WeakHessian.HeatFlow.CheegerScaledResolventNonneg

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional WeakHessianTransport
open scoped Topology NNReal ENNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma tendsto_integral_bounded_pairing_L1 {us : ℕ → Lp ℝ 2 m} {u : Lp ℝ 2 m}
    (hi : Integrable u m) (his : ∀ n,Integrable (us n) m)
    (hlim : Tendsto (fun n => ∫ x,‖us n x-u x‖ ∂m) atTop (𝓝 0)) (f : X →ᵇ ℝ) :
    Tendsto (fun n => ∫ x,us n x*f x ∂m) atTop (𝓝 (∫ x,u x*f x ∂m)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => ?_) (by simpa using hlim.const_mul ‖f‖)
  simpa only [sub_self,norm_zero,zero_mul,zero_add,Real.norm_eq_abs] using
    integral_bounded_pairing_diff_bound hi (his n) f f

lemma CurvatureDimension.cheegerHeat_entropy_hopf_generator {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m) (hA : Integrable A m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    {b : ℝ} (hb : 0 < b) (f : X →ᵇ ℝ) {J : ℝ≥0} (hf : LipschitzWith J f) :
    (∫ x,cheegerHeat h b u x*boundedHopfMap f b x ∂m)-(∫ x,u x*f x ∂m) ≤
      ((∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (cheegerHeat h b u x) ∂m))/2 := by
  have H := hcd.cheegerHeat_fisher_finite_action hN hfull hfin o h hu hun hi hV hU hD hw hb.le
  have HH := hcd.cheegerHeat_hopf_action hN hfull hfin o h hu hun hi hA hf hb H.1 (H.2.1.div_const 2)
  rwa [intervalIntegral.integral_div,hcd.cheegerHeat_entropy_dissipation hN hfull hfin o h hu hun hi hV hU hD hw hb.le] at HH

lemma CurvatureDimension.cheegerHeat_entropy_hopf_resolvents {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    {ts : ℕ → ℝ} (hpos : ∀ n,0 < ts n)
    (hsmall : ∀ n,ts n*(L:ℝ)^2 ≤ 1/2) (hlim : Tendsto ts atTop (𝓝 0))
    {b : ℝ} (hb : 0 < b) (f : X →ᵇ ℝ) {J : ℝ≥0} (hf : LipschitzWith J f) :
    (∫ x,cheegerHeat h b u x*boundedHopfMap f b x ∂m)-(∫ x,u x*f x ∂m) ≤
      ((∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (cheegerHeat h b u x) ∂m))/2 := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfin _ Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy h
  let us : ℕ → Lp ℝ 2 m := fun n => (Q.scale (hpos n)).resolventLinear u
  let As : ℕ → Lp ℝ 2 m := fun n => (ts n)⁻¹ • (us n-u)
  have hsmall' (n : ℕ) : ts n*(L:ℝ)^2 < 1 := (hsmall n).trans_lt (by norm_num)
  have hus (n : ℕ) : Q.IsFormGenerator (us n) (As n) :=
    (Q.scaled_resolvent_iff (hpos n) u (us n)).mp rfl
  have hW (n : ℕ) : MemLp (fun x => us n x*Real.exp (V x)) 2 m :=
    hcd.cheegerResolvent_weighted hfin o h u (hpos n) hV hU (hsmall' n)
  have hWnorm (n : ℕ) : ‖(hW n).toLp (fun x => us n x*Real.exp (V x))‖ ≤
      2*‖hU.toLp (fun x => u x*Real.exp (V x))‖ := by
    apply (hcd.cheegerResolvent_weighted_norm hfin o h u (hpos n) hV hU (hsmall' n)).trans
    apply (div_le_iff₀ (sub_pos.mpr (hsmall' n))).mpr
    have H := mul_le_mul_of_nonneg_left (hsmall n) (norm_nonneg (hU.toLp _))
    nlinarith
  have hAw (n : ℕ) : MemLp (fun x => As n x*Real.exp (V x)) 2 m := scaled_generator_weighted hU (hW n)
  have hAn (n : ℕ) : Integrable (As n) m := integrable_of_memLp_mul_exp (hAw n) hdecay
  have his (n : ℕ) : Integrable (us n) m := integrable_of_memLp_mul_exp (hW n) hdecay
  have hn (n : ℕ) : ∀ᵐ x ∂m,0 ≤ us n x := cheeger_scaled_resolvent_nonneg h (hpos n) u hun
  have hm (n : ℕ) : (∫ x,us n x ∂m) = ∫ x,u x ∂m :=
    hcd.cheegerResolvent_mass_localized hfin o h u (hpos n) hV hU hdecay (hsmall' n)
  have hum : Tendsto us atTop (𝓝 u) := Q.scaled_resolvent_tendsto (cheeger_domain_dense h) hpos hlim u
  have hut : Tendsto (fun n => cheegerHeat h b (us n)) atTop (𝓝 (cheegerHeat h b u)) :=
    (cheegerHeat h b).continuous.continuousAt.tendsto.comp hum
  have htn (n : ℕ) : ∀ᵐ x ∂m,0 ≤ cheegerHeat h b (us n) x := cheegerHeat_nonneg h hb.le _ (hn n)
  have hmu : (∫ x,cheegerHeat h b u x ∂m) = ∫ x,u x ∂m := (hcd.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hi hb.le).2
  have hmt (n : ℕ) : (∫ x,cheegerHeat h b (us n) x ∂m) = ∫ x,cheegerHeat h b u x ∂m := by
    rw [(hcd.cheegerHeat_mass_nonneg hN hfull hfin o h (us n) (hn n) (his n) hb.le).2,hm n,hmu]
  have htu := cheegerHeat_nonneg h hb.le u hun
  have hti : Integrable (cheegerHeat h b u) m := (cheegerHeat_integrable hfin o h u hi hb.le).1
  have htis (n : ℕ) : Integrable (cheegerHeat h b (us n)) m := (cheegerHeat_integrable hfin o h (us n) (his n) hb.le).1
  have hL1 := tendsto_integral_norm_sub_of_nonneg_mass hum hn hun his hi (by simpa only [hm] using tendsto_const_nhds)
  have hL1t := tendsto_integral_norm_sub_of_nonneg_mass hut htn htu htis hti (by simpa only [hmt] using tendsto_const_nhds)
  have hp0 := tendsto_integral_bounded_pairing_L1 hi his hL1 f
  have hpt := tendsto_integral_bounded_pairing_L1 hti htis hL1t (boundedHopfMap f b)
  have hWt (n : ℕ) := (hcd.cheegerHeat_weighted hfin o h (us n) hV (hW n) hb.le).1
  have hUt := (hcd.cheegerHeat_weighted hfin o h u hV hU hb.le).1
  have hWtnorm (n : ℕ) : ‖(hWt n).toLp (fun x => cheegerHeat h b (us n) x*Real.exp (V x))‖ ≤
      (2*‖hU.toLp (fun x => u x*Real.exp (V x))‖)*Real.exp ((L:ℝ)^2*b) := by
    exact (hcd.cheegerHeat_weighted_norm hfin o h (us n) hV (hW n) hb.le).trans
      (mul_le_mul_of_nonneg_right (hWnorm n) (Real.exp_pos _).le)
  have hecause {vs : ℕ → Lp ℝ 2 m} {v : Lp ℝ 2 m}
      (hv : Tendsto vs atTop (𝓝 v)) (hvpos : ∀ᵐ x ∂m,0 ≤ v x)
      (hvs : ∀ n,∀ᵐ x ∂m,0 ≤ vs n x) (hvi : Integrable v m) (hvsi : ∀ n,Integrable (vs n) m)
      (hvm : ∀ n,(∫ x,vs n x ∂m) = ∫ x,v x ∂m)
      (hvW : MemLp (fun x => v x*Real.exp (V x)) 2 m)
      (hvsW : ∀ n,MemLp (fun x => vs n x*Real.exp (V x)) 2 m)
      {C : ℝ} (hvC : ‖hvW.toLp _‖ ≤ C) (hvsC : ∀ n,‖(hvsW n).toLp _‖ ≤ C) :
      Tendsto (fun n => ∫ x,reducedEntropy (vs n x) ∂m) atTop (𝓝 (∫ x,reducedEntropy (v x) ∂m)) := by
    have hroot := integrable_sqrt_weighted (Lp.aestronglyMeasurable v) hvpos hvW hhalf hhalfi
    have hroots (n : ℕ) := integrable_sqrt_weighted (Lp.aestronglyMeasurable (vs n)) (hvs n) (hvsW n) hhalf hhalfi
    apply tendsto_integral_reducedEntropy_of_sqrt_bound hv hvpos hvs hvi hvsi hvm hroot.1 (fun n => (hroots n).1)
      (C := (C*‖hhalf.toLp _‖+(∫ x,Real.exp (-(V x/2)) ∂m))/2)
    · exact hroot.2.trans (by gcongr)
    · intro n
      exact (hroots n).2.trans (by gcongr; exact hvsC n)
  have he0 := hecause hum hun hn hi his hm hU hW (C := 2*‖hU.toLp _‖) (by nlinarith [norm_nonneg (hU.toLp _)]) hWnorm
  have het := hecause hut htu htn hti htis hmt hUt hWt
    (C := (2*‖hU.toLp _‖)*Real.exp ((L:ℝ)^2*b))
    ((hcd.cheegerHeat_weighted_norm hfin o h u hV hU hb.le).trans (by
      gcongr; nlinarith [norm_nonneg (hU.toLp _)])) hWtnorm
  apply le_of_tendsto_of_tendsto (hpt.sub hp0) ((he0.sub het).div_const 2)
  exact Eventually.of_forall fun n => hcd.cheegerHeat_entropy_hopf_generator hN hfull hfin o h
    (hus n) (hn n) (his n) (hAn n) hV (hW n) hD hw hb f hf
end WeakHessian

end
end InlinedFile0

end OAI
