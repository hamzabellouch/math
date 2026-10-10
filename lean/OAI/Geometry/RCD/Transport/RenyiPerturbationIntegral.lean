import OAI.Geometry.RCD.Transport.RenyiPerturbation

namespace OAI

/-! # Strict Rényi improvement by a bounded replacement density -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem exists_renyi_increasing_perturbation
    (μ : Measure X) [IsFiniteMeasure μ] {ρ h : X → ℝ}
    (hρ : Measurable ρ) (hh : Measurable h)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hh0 : ∀ x, 0 ≤ h x) (hρi : Integrable ρ μ)
    {q C D : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 0 < C) (hD : C < D)
    (hhC : ∀ x, h x ≤ C) (hpos : μ {x | D ≤ ρ x} ≠ 0)
    (hmass : (∫ x, h x ∂μ) = ∫ x in {x | C < ρ x}, ρ x ∂μ) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      Integrable (fun x => (entropyPerturb C a (ρ x) (h x))^q) μ ∧
      (∫ x, (ρ x)^q ∂μ) < ∫ x, (entropyPerturb C a (ρ x) (h x))^q ∂μ := by
  classical
  let A := {x | C < ρ x}
  let T := {x | D ≤ ρ x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hρ
  have hT : MeasurableSet T := measurableSet_le measurable_const hρ
  let m := ∫ x, h x ∂μ
  let b : ℝ → ℝ := fun a =>
    ((C*(1+a))^(q-1)-((1-a)*C)^(q-1))*m+
      (((1-a)*C)^(q-1)-((1-a)*D)^(q-1))*(D-C)*μ.real T
  have hp : ContinuousAt (fun a : ℝ => (C*(1+a))^(q-1)) 0 :=
    (by fun_prop : ContinuousAt (fun a : ℝ => C*(1+a)) 0).rpow_const
      (Or.inl (by simpa using hC.ne'))
  have hm : ContinuousAt (fun a : ℝ => ((1-a)*C)^(q-1)) 0 :=
    (by fun_prop : ContinuousAt (fun a : ℝ => (1-a)*C) 0).rpow_const
      (Or.inl (by simpa using hC.ne'))
  have hd : ContinuousAt (fun a : ℝ => ((1-a)*D)^(q-1)) 0 :=
    (by fun_prop : ContinuousAt (fun a : ℝ => (1-a)*D) 0).rpow_const
      (Or.inl (by simpa using (hC.trans hD).ne'))
  have hb : ContinuousAt b 0 :=
    ((hp.sub hm).mul continuousAt_const).add
      (((hm.sub hd).mul continuousAt_const).mul continuousAt_const)
  have hb0 : 0 < b 0 := by
    have hgap := sub_pos.mpr (Real.rpow_lt_rpow_of_neg hC hD (by linarith : q-1 < 0))
    have hv : 0 < μ.real T := ENNReal.toReal_pos hpos (measure_ne_top μ T)
    simpa only [b,add_zero,sub_zero,mul_one,one_mul,sub_self,zero_mul,zero_add] using
      mul_pos (mul_pos hgap (sub_pos.mpr hD)) hv
  have haevent : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a ∧ a < 1 ∧ 0 < b a := by
    filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      (hb.tendsto.eventually (lt_mem_nhds hb0)).filter_mono nhdsWithin_le_nhds] with a ha0 ha1 hab
    exact ⟨ha0,ha1,hab⟩
  obtain ⟨a,ha0,ha1,hab⟩ := haevent.exists
  have hhi : Integrable h μ := Integrable.of_bound hh.aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hh0 x)] using hhC x)
  have hAi : Integrable (A.indicator ρ) μ := hρi.indicator hA
  have hTi : Integrable (T.indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator hT
  have hpm : Measurable (fun x => entropyPerturb C a (ρ x) (h x)) := by
    change Measurable (A.piecewise (fun x => (1-a)*ρ x+a*h x) (fun x => ρ x+a*h x))
    exact ((hρ.const_mul _).add (hh.const_mul _)).piecewise hA (hρ.add (hh.const_mul _))
  have hpi : Integrable (fun x => entropyPerturb C a (ρ x) (h x)) μ := by
    apply ((hρi.sub (hAi.const_mul a)).add (hhi.const_mul a)).congr
    filter_upwards [] with x
    by_cases hx : x∈A
    · simp only [Pi.add_apply,Pi.sub_apply,indicator_of_mem hx]
      change C < ρ x at hx
      rw [entropyPerturb,ite_eq_left hx]
      ring
    · simp only [Pi.add_apply,Pi.sub_apply,indicator_of_notMem hx,mul_zero,sub_zero]
      change ¬C < ρ x at hx
      rw [entropyPerturb,ite_eq_right hx]
  have hp0 (x : X) : 0 ≤ entropyPerturb C a (ρ x) (h x) :=
    entropyPerturb_nonneg ha0.le ha1.le (hρ0 x) (hh0 x)
  have hip := integrable_density_power μ _ hpm hpi (Eventually.of_forall hp0) hq0.le hq1.le
  have hir := integrable_density_power μ _ hρ hρi (Eventually.of_forall hρ0) hq0.le hq1.le
  let cp := (C*(1+a))^(q-1)
  let cm := ((1-a)*C)^(q-1)
  let cd := ((1-a)*D)^(q-1)
  let F := fun x => a*q*(cp*h x-cm*A.indicator ρ x+(cm-cd)*(D-C)*T.indicator (fun _ => 1) x)
  have hFi : Integrable F μ :=
    (((hhi.const_mul cp).sub (hAi.const_mul cm)).add
      (hTi.const_mul ((cm-cd)*(D-C)))).const_mul (a*q)
  have hF (x : X) : F x ≤ (entropyPerturb C a (ρ x) (h x))^q-(ρ x)^q := by
    simpa only [F,cp,cm,cd,A,T,Set.indicator_apply,mem_ofPred_eq,renyiPerturbLower] using
      renyiPerturb_power_lower hq0 hq1 hC hD ha0.le ha1 (hρ0 x) (hh0 x) (hhC x)
  have hIA : (∫ x, A.indicator ρ x ∂μ) = m := (integral_indicator hA).trans hmass.symm
  have hIT : (∫ x, T.indicator (fun _ => (1:ℝ)) x ∂μ) = μ.real T := by
    rw [integral_indicator hT,integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one]
  have hIF : (∫ x, F x ∂μ) = a*q*b a := by
    dsimp only [F]
    rw [integral_const_mul,integral_add,integral_sub,integral_const_mul,
      integral_const_mul,integral_const_mul,hIA,hIT]
    · dsimp only [b,cp,cm,cd]
      ring
    · exact hhi.const_mul cp
    · exact hAi.const_mul cm
    · exact (hhi.const_mul cp).sub (hAi.const_mul cm)
    · exact hTi.const_mul ((cm-cd)*(D-C))
  have hle := integral_mono hFi (hip.sub hir) hF
  change (∫ x, F x ∂μ) ≤ ∫ x, (entropyPerturb C a (ρ x) (h x))^q-(ρ x)^q ∂μ at hle
  rw [integral_sub hip hir,hIF] at hle
  refine ⟨a,ha0,ha1,hip,?_⟩
  have hpab : 0 < a*q*b a := mul_pos (mul_pos ha0 hq0) hab
  linarith

end RegularPointCoordinates

end

end OAI
