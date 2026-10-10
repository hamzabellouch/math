import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerScaledResolventNonneg
import OAI.Geometry.WeakHessian.LocalBounds.IntegratedEVI
import OAI.Geometry.WeakHessian.LocalBounds.CostContinuity
import OAI.Geometry.WeakHessian.Entropy.EntropyStability

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile56
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma RCD.cheegerHeat_comparison_resolvents {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m) (hmass : ∫ x,u x ∂m = 1)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,|u x| ≤ B)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (ν : ProbabilityMeasure X) (T : ℝ≥0) (hT : 0 < T)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    (hW1 : MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    {ts : ℕ → ℝ} (hpos : ∀ n,0 < ts n)
    (hsmall : ∀ n,ts n*(L:ℝ)^2 ≤ 1/2) (hlim : Tendsto ts atTop (𝓝 0))
    {b : ℝ} (hb : 0 ≤ b) :
    (Real.exp (K*b)*quadraticWassersteinSq (μ b:Measure X) (ν:Measure X)-
      quadraticWassersteinSq (μ 0:Measure X) (ν:Measure X))/2 ≤
      ∫ t in 0..b,Real.exp (K*t)*(entropyReal m (ν:Measure X)-entropyReal m (μ t:Measure X)) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfin _ Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy h
  let us : ℕ → Lp ℝ 2 m := fun n => (Q.scale (hpos n)).resolventLinear u
  let As : ℕ → Lp ℝ 2 m := fun n => (ts n)⁻¹ • (us n-u)
  have hsmall' (n : ℕ) : ts n*(L:ℝ)^2 < 1 := (hsmall n).trans_lt (by norm_num)
  have hus (n : ℕ) : Q.IsFormGenerator (us n) (As n) :=
    (Q.scaled_resolvent_iff (hpos n) u (us n)).mp rfl
  have hUs (n : ℕ) : MemLp (fun x => us n x*Real.exp (V x)) 2 m :=
    hrcd.1.cheegerResolvent_weighted hfin o h u (hpos n) hV hU (hsmall' n)
  have hUsnorm (n : ℕ) : ‖(hUs n).toLp _‖ ≤ 2*‖hU.toLp _‖ := by
    apply (hrcd.1.cheegerResolvent_weighted_norm hfin o h u (hpos n) hV hU (hsmall' n)).trans
    apply (div_le_iff₀ (sub_pos.mpr (hsmall' n))).mpr
    have H := mul_le_mul_of_nonneg_left (hsmall n) (norm_nonneg (hU.toLp _))
    nlinarith
  have hAw (n : ℕ) : MemLp (fun x => As n x*Real.exp (V x)) 2 m := scaled_generator_weighted hU (hUs n)
  have his (n : ℕ) : Integrable (us n) m := integrable_of_memLp_mul_exp (hUs n) hdecay
  have hn (n : ℕ) : ∀ᵐ x ∂m,0 ≤ us n x := cheeger_scaled_resolvent_nonneg h (hpos n) u hun
  have hbn (n : ℕ) : ∀ᵐ x ∂m,us n x ≤ B :=
    (cheeger_scaled_resolvent_bounded h (hpos n) hB u huB).mono fun x hx => (le_abs_self _).trans hx
  have hm (n : ℕ) : (∫ x,us n x ∂m) = 1 :=
    (hrcd.1.cheegerResolvent_mass_localized hfin o h u (hpos n) hV hU hdecay (hsmall' n)).trans hmass
  have hum : Tendsto us atTop (𝓝 u) := Q.scaled_resolvent_tendsto (cheeger_domain_dense h) hpos hlim u
  let μs (n : ℕ) (t : ℝ) : ProbabilityMeasure X :=
    ⟨densityMeasure m (cheegerHeat h (max t 0) (us n)),
      hrcd.1.cheegerHeat_probability hN hfull hfin o h (us n) (hn n) (hm n) (le_max_right t 0)⟩
  have hμs (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
      (μs n t:Measure X) = densityMeasure m (cheegerHeat h t (us n)) := by
    simp only [μs,max_eq_left ht]
    rfl
  have hUt (t : ℝ) (ht : 0 ≤ t) := (hrcd.1.cheegerHeat_weighted hfin o h u hV hU ht).1
  have hUst (n : ℕ) (t : ℝ) (ht : 0 ≤ t) := (hrcd.1.cheegerHeat_weighted hfin o h (us n) hV (hUs n) ht).1
  have hUstnorm (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
      ‖(hUst n t ht).toLp _‖ ≤ (2*‖hU.toLp _‖)*Real.exp ((L:ℝ)^2*t) :=
    (hrcd.1.cheegerHeat_weighted_norm hfin o h (us n) hV (hUs n) ht).trans
      (mul_le_mul_of_nonneg_right (hUsnorm n) (Real.exp_pos _).le)
  have hnU (t : ℝ) (ht : 0 ≤ t) := cheegerHeat_nonneg h ht u hun
  have hnUs (n : ℕ) (t : ℝ) (ht : 0 ≤ t) := cheegerHeat_nonneg h ht (us n) (hn n)
  have hiU (t : ℝ) (ht : 0 ≤ t) := (cheegerHeat_integrable hfin o h u hi ht).1
  have hiUs (n : ℕ) (t : ℝ) (ht : 0 ≤ t) := (cheegerHeat_integrable hfin o h (us n) (his n) ht).1
  have htu (t : ℝ) : Tendsto (fun n => cheegerHeat h t (us n)) atTop (𝓝 (cheegerHeat h t u)) :=
    (cheegerHeat h t).continuous.continuousAt.tendsto.comp hum
  have he (t : ℝ) (ht : 0 ≤ t) : entropyReal m (μ t:Measure X) = (∫ x,reducedEntropy (cheegerHeat h t u x) ∂m)+1 :=
    entropyReal_eq_reducedDensity _ (hnU t ht) (hiU t ht)
      (integrable_reducedEntropy (Lp.memLp _) (hnU t ht) (weighted_pairing (hUt t ht) hD).1 hw) (μ t) (hμ t ht)
  have hes (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : entropyReal m (μs n t:Measure X) =
      (∫ x,reducedEntropy (cheegerHeat h t (us n) x) ∂m)+1 :=
    entropyReal_eq_reducedDensity _ (hnUs n t ht) (hiUs n t ht)
      (integrable_reducedEntropy (Lp.memLp _) (hnUs n t ht) (weighted_pairing (hUst n t ht) hD).1 hw) (μs n t) (hμs n t ht)
  have hcost (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun n => quadraticWassersteinSq (μs n t:Measure X) (ν:Measure X)) atTop
        (𝓝 (quadraticWassersteinSq (μ t:Measure X) (ν:Measure X))) :=
    hrcd.1.cost_tendsto_density hfin o T (htu t) (hnU t ht) (fun n => hnUs n t ht) (hiU t ht)
      (fun n => hiUs n t ht) (μ t) (fun n => μs n t) ν (hμ t ht) (fun n => hμs n t ht)
      (Measure.absolutelyContinuous_of_le_smul hdν) hsν hV.continuous.measurable (hUt t ht)
      (fun n => hUst n t ht) (Eventually.of_forall fun n => hUstnorm n t ht) hW
  have hEnt (t : ℝ) (ht : 0 ≤ t) : Tendsto (fun n => entropyReal m (μs n t:Measure X)) atTop
      (𝓝 (entropyReal m (μ t:Measure X))) := by
    simp_rw [he t ht,hes _ t ht]
    apply Tendsto.add_const
    apply integral_reducedEntropy_tendsto_weighted hhalf hhalfi (htu t) (hnU t ht) (fun n => hnUs n t ht)
      (hiU t ht) (fun n => hiUs n t ht) (fun n => by
        rw [(hrcd.1.cheegerHeat_mass_nonneg hN hfull hfin o h (us n) (hn n) (his n) ht).2,
          (hrcd.1.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hi ht).2,hm n,hmass])
      (hUt t ht) (fun n => hUst n t ht) (C := (2*‖hU.toLp _‖)*Real.exp ((L:ℝ)^2*t))
    · exact (hrcd.1.cheegerHeat_weighted_norm hfin o h u hV hU ht).trans (by
        gcongr; nlinarith [norm_nonneg (hU.toLp _)])
    · exact fun n => hUstnorm n t ht
  let D := ‖u‖^2/2+(2*‖hU.toLp _‖)*Real.exp ((L:ℝ)^2*b)*‖hD.toLp _‖+(∫ x,Real.exp (-V x) ∂m)+1
  have hEntbound (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 b) : |entropyReal m (μs n t:Measure X)| ≤ D := by
    rw [hes n t ht.1]
    have H := integral_reducedEntropy_weighted_bound _ (hnUs n t ht.1) (hUst n t ht.1) hD hw
    have hu1 : ‖us n‖ ≤ ‖u‖ := by
      exact ((Q.scale (hpos n)).resolventLinear.le_opNorm u).trans
        ((mul_le_mul_of_nonneg_right (Q.scale (hpos n)).resolvent_norm_le_one (norm_nonneg u)).trans_eq (one_mul _))
    have ht1 : ‖cheegerHeat h t (us n)‖ ≤ ‖us n‖ := by
      simpa only [map_zero,dist_zero_right] using cheegerHeat_contractive h ht.1 (us n) 0
    have H' : |∫ x,reducedEntropy (cheegerHeat h t (us n) x) ∂m| ≤ D-1 := by
      apply H.trans
      dsimp only [D]
      have hnrm := ht1.trans hu1
      have hwgt := hUstnorm n t ht.1
      have hexp : Real.exp ((L:ℝ)^2*t) ≤ Real.exp ((L:ℝ)^2*b) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg _))
      nlinarith [mul_le_mul_of_nonneg_right hwgt (norm_nonneg (hD.toLp _)),
        mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 2*‖hU.toLp _‖*‖hD.toLp _‖),
        sq_le_sq₀ (norm_nonneg _) (norm_nonneg u) |>.mpr hnrm]
    calc
      _ ≤ |∫ x,reducedEntropy (cheegerHeat h t (us n) x) ∂m|+|1| := abs_add_le _ _
      _ ≤ D := by rw [abs_one]; linarith
  have hEc (n : ℕ) := hrcd.1.cheegerHeat_entropy_continuousOn hN hfull hfin o h (hus n)
    (hn n) (his n) hV (hUs n) hD hw (μs n) (hμs n) hb
  have hright : Tendsto (fun n => ∫ t in Icc 0 b,Real.exp (K*t)*(entropyReal m (ν:Measure X)-entropyReal m (μs n t:Measure X))) atTop
      (𝓝 (∫ t in Icc 0 b,Real.exp (K*t)*(entropyReal m (ν:Measure X)-entropyReal m (μ t:Measure X)))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => Real.exp (|K| * b)*(|entropyReal m (ν:Measure X)|+D))
    · intro n
      exact ((by fun_prop : ContinuousOn (fun t : ℝ => Real.exp (K*t)) (Icc 0 b)).fun_mul
        (continuousOn_const.sub (hEc n))).aestronglyMeasurable measurableSet_Icc
    · exact integrable_const _
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have H : K*t ≤ |K| *b := (mul_le_mul_of_nonneg_right (le_abs_self K) ht.1).trans
        (mul_le_mul_of_nonneg_left ht.2 (abs_nonneg K))
      rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_eq_abs]
      apply mul_le_mul (Real.exp_le_exp.mpr H) ?_ (abs_nonneg _) (Real.exp_pos _).le
      have hab : |entropyReal m (ν:Measure X)-entropyReal m (μs n t:Measure X)| ≤
          |entropyReal m (ν:Measure X)|+|entropyReal m (μs n t:Measure X)| := by
        simpa only [sub_zero,zero_sub,abs_neg] using
          (abs_sub_le (entropyReal m (ν:Measure X)) 0 (entropyReal m (μs n t:Measure X)))
      exact hab.trans (add_le_add le_rfl (hEntbound n t ht))
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact ((tendsto_const_nhds (x := entropyReal m (ν:Measure X))).sub (hEnt t ht.1)).const_mul _
  have heq (f : ℝ → ℝ) : (∫ t in Icc 0 b,f t) = ∫ t in 0..b,f t := by
    rw [intervalIntegral.integral_of_le hb,integral_Icc_eq_integral_Ioc]
  simp_rw [heq] at hright
  apply le_of_tendsto_of_tendsto (((hcost b hb).const_mul (Real.exp (K*b))).sub (hcost 0 le_rfl) |>.div_const 2) hright
  exact Eventually.of_forall fun n => hrcd.cheegerHeat_comparison_integrated hN hfull hfin o h (hus n)
    (hn n) (his n) hB (hbn n) hV (hUs n) (hAw n) hD hw (μs n) (hμs n) ν T hT hsν hCt hdν hW hW1 hb
end WeakHessian

end
end InlinedFile56

end OAI
