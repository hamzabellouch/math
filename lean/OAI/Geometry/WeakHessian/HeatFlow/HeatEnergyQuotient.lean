import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CheegerEnergyConst
import OAI.Geometry.WeakHessian.LocalBounds.SubConst
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatContinuous

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile103
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma cheegerHeat_deriv_right_of_generator (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m} {t : ℝ} (ht : 0 ≤ t)
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator (cheegerHeat h t u) A) :
    HasDerivWithinAt (fun s => cheegerHeat h s u) A (Ici t) t := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  have hg := (cheeger_closedQuadraticEnergy h).heat_deriv_form_zero m (cheeger_domain_dense h) hu
  change HasDerivWithinAt (fun r => cheegerHeat h r (cheegerHeat h t u)) A (Ici 0) 0 at hg
  have hc : HasDerivWithinAt (fun s : ℝ => s-t) 1 (Ici t) t :=
    (hasDerivWithinAt_id t (Ici t)).sub_const t
  have H := hg.scomp_of_eq (h := fun s : ℝ => s-t) t hc
    (show MapsTo (fun s : ℝ => s-t) (Ici t) (Ici 0) from
      fun s hs => (show 0 ≤ s-t from sub_nonneg.mpr hs)) (by simp)
  simp only [one_smul,Function.comp_def] at H
  apply H.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have he := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T u)
      (cheegerHeat_add h (sub_nonneg.mpr hs) ht)
    simpa only [mul_apply_eq_comp,sub_add_cancel] using he
  · rw [sub_self,cheegerHeat_zero,one_apply_eq_self]

lemma cheegerHeat_energy_quotient (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t) :
    (cheegerEnergy m (cheegerHeat h t u : X → ℝ)).toReal ≤
      (⟪u,u⟫_ℝ-⟪u,cheegerHeat h t u⟫_ℝ)/(2*t) := by
  let Q := cheeger_closedQuadraticEnergy h
  let E := (cheegerEnergy m (cheegerHeat h t u : X → ℝ)).toReal
  let J (s : ℝ) := ⟪cheegerHeat h s u,cheegerHeat h s u⟫_ℝ
  have hJ : ContinuousOn J (Ici 0) :=
    (cheegerHeat_continuousOn hfin h u).inner (cheegerHeat_continuousOn hfin h u)
  have H (a : ℝ) (ha : 0 < a) (hat : a ≤ t) : J t ≤ J a-4*E*(t-a) := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary (f := J)
      (B := fun z => J a-4*E*(z-a)) (B' := fun _ => -4*E)
      (hJ.mono (fun _ hx => ha.le.trans hx.1)) (by simp) (by fun_prop)
      (fun x _ => by
        convert! ((((hasDerivAt_id x).sub_const a).const_mul (4*E)).const_sub (J a)).hasDerivWithinAt (s := Ici x) using 1
        simp only [mul_one]
        ring)
      _ ⟨hat,le_rfl⟩
    intro s hs r hr
    obtain ⟨A,hA⟩ := Q.heat_hasFormGenerator m (ha.trans_le hs.1) u
    have hd := cheegerHeat_deriv_right_of_generator hfin h (ha.le.trans hs.1) hA
    have hds : HasDerivWithinAt J (-4*(cheegerEnergy m (cheegerHeat h s u : X → ℝ)).toReal) (Ici s) s := by
      have HH := hd.inner ℝ hd
      rw [real_inner_comm A (cheegerHeat h s u)] at HH
      have HE := Q.formGenerator_energy hA
      change 2*(cheegerEnergy m (cheegerHeat h s u : X → ℝ)).toReal = -⟪A,cheegerHeat h s u⟫_ℝ at HE
      convert! HH using 1
      linarith
    have he : cheegerEnergy m (cheegerHeat h t u : X → ℝ) ≤ cheegerEnergy m (cheegerHeat h s u : X → ℝ) := by
      have HH := cheegerHeat_energy_le h (sub_nonneg.mpr hs.2.le) (cheegerHeat h s u)
      have heq := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T u)
        (cheegerHeat_add h (sub_nonneg.mpr hs.2.le) (ha.le.trans hs.1))
      rw [sub_add_cancel] at heq
      change cheegerHeat h t u = cheegerHeat h (t-s) (cheegerHeat h s u) at heq
      rwa [← heq] at HH
    have heb : E ≤ (cheegerEnergy m (cheegerHeat h s u : X → ℝ)).toReal := ENNReal.toReal_mono hA.1.ne he
    exact hds.liminf_right_slope_le (lt_of_le_of_lt (by change -4*(cheegerEnergy m (cheegerHeat h s u : X → ℝ)).toReal ≤ -4*E; linarith) hr)
  have hh : J t ≤ J 0-4*E*t := by
    have hid : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hc := (hJ 0 (by simp)).mono (Ioi_subset_Ici_self (a := (0:ℝ)))
    change Tendsto J (𝓝[>] 0) (𝓝 (J 0)) at hc
    have hl : Tendsto (fun a : ℝ => J a-4*E*(t-a)) (𝓝[>] 0) (𝓝 (J 0-4*E*t)) := by
      simpa only [sub_zero] using hc.sub (((tendsto_const_nhds (x := t)).sub hid).const_mul (4*E))
    apply ge_of_tendsto hl
    filter_upwards [self_mem_nhdsWithin,hid.eventually_lt_const ht] with a ha hat
    exact H a ha hat.le
  have hnorm : 0 ≤ ⟪u-cheegerHeat h t u,u-cheegerHeat h t u⟫_ℝ := real_inner_self_nonneg
  simp only [inner_sub_left,inner_sub_right,real_inner_comm (cheegerHeat h t u) u] at hnorm
  simp only [J,cheegerHeat_zero,one_apply_eq_self] at hh
  apply (le_div_iff₀ (by positivity : 0 < 2*t)).mpr
  dsimp only [E] at hh
  nlinarith [real_inner_comm u (cheegerHeat h t u)]

lemma cheegerEnergy_le_of_heat_quotient (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {C : ℝ}
    (hb : ∀ t : ℝ,0 < t → t ≤ 1 → ⟪u,u⟫_ℝ-⟪u,cheegerHeat h t u⟫_ℝ ≤ C*t) :
    cheegerEnergy m (u : X → ℝ) ≤ ENNReal.ofReal (C/2) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  have hbound (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
      cheegerEnergy m (cheegerHeat h t u : X → ℝ) ≤ ENNReal.ofReal (C/2) := by
    obtain ⟨A,hA⟩ := (cheeger_closedQuadraticEnergy h).heat_hasFormGenerator m ht u
    have H := (cheegerHeat_energy_quotient hfin h u ht).trans
      (show (⟪u,u⟫_ℝ-⟪u,cheegerHeat h t u⟫_ℝ)/(2*t) ≤ C/2 by
        apply (div_le_iff₀ (by positivity : 0 < 2*t)).mpr
        nlinarith [hb t ht ht1])
    exact (ENNReal.le_ofReal_iff_toReal_le hA.1.ne (ENNReal.toReal_nonneg.trans H)).mpr H
  apply ((cheeger_closedQuadraticEnergy h).lowerSemicontinuous.isClosed_preimage (ENNReal.ofReal (C/2))).mem_of_tendsto
    ((cheegerHeat_strong_zero h u).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self))
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0)).eventually_lt_const (by norm_num : (0:ℝ)<1)] with t ht ht1
  exact hbound t ht ht1.le
lemma cheegerEnergy_le_of_eventual_heat_quotient (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {C : ℝ}
    (hb : ∀ᶠ t : ℝ in 𝓝[>] 0, ⟪u,u⟫_ℝ-⟪u,cheegerHeat h t u⟫_ℝ ≤ C*t) :
    cheegerEnergy m (u : X → ℝ) ≤ ENNReal.ofReal (C/2) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  apply ((cheeger_closedQuadraticEnergy h).lowerSemicontinuous.isClosed_preimage (ENNReal.ofReal (C/2))).mem_of_tendsto
    ((cheegerHeat_strong_zero h u).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self))
  filter_upwards [self_mem_nhdsWithin,hb] with t ht hb
  change 0 < t at ht
  obtain ⟨A,hA⟩ := (cheeger_closedQuadraticEnergy h).heat_hasFormGenerator m ht u
  have H := (cheegerHeat_energy_quotient hfin h u ht).trans
    (show (⟪u,u⟫_ℝ-⟪u,cheegerHeat h t u⟫_ℝ)/(2*t) ≤ C/2 by
      apply (div_le_iff₀ (by positivity : 0 < 2*t)).mpr
      nlinarith)
  exact (ENNReal.le_ofReal_iff_toReal_le hA.1.ne (ENNReal.toReal_nonneg.trans H)).mpr H

end WeakHessian

end
end InlinedFile103

end OAI
