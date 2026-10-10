import OAI.Analysis.BernoulliCone.ExteriorCalibration

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

def upperFlux (p:Space 7×ℝ) : Space 7 :=
  if U p.1<p.2 then
    κ • (if Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≤1
      then gradient smoothCap ((upperParameter p.1 p.2)⁻¹ • p.1)
      else gradient outerSigned ((upperParameter p.1 p.2)⁻¹ • p.1))
  else 0
lemma upperParameter_signed_pos {p:Space 7×ℝ} (hp:U p.1<p.2) :
    0<upperSigned ((upperParameter p.1 p.2)⁻¹ • p.1) := by
  obtain ⟨hl,he⟩:=upperParameter_spec hp
  have hpos:0<upperFamily (upperParameter p.1 p.2) p.1:=by
    rw [he]; exact (U_nonneg _).trans_lt hp
  have hh:0 < max (upperSigned ((upperParameter p.1 p.2)⁻¹ • p.1)) 0:=
    pos_of_mul_pos_right hpos (mul_nonneg κ_pos.le hl.le)
  simpa using hh
lemma upperFlux_uniform_bound : ∃C:ℝ,0<C ∧ ∀p:Space 7×ℝ,‖upperFlux p‖≤C := by
  obtain ⟨C,hC,hcap⟩:=cap_gradient_uniform_bound
  obtain ⟨D,hD,hext⟩:=outer_gradient_uniform_bound
  refine ⟨κ*(C+D),mul_pos κ_pos (add_pos hC hD),?_⟩
  intro p
  by_cases hp:U p.1<p.2
  · have hpos:=upperParameter_signed_pos hp
    rw [upperFlux,ite_eq_left hp,norm_smul,Real.norm_eq_abs,abs_of_pos κ_pos]
    apply mul_le_mul_of_nonneg_left _ κ_pos.le
    split_ifs with hq
    · rw [upperSigned_cap hq] at hpos
      exact (hcap _ hq hpos).trans (by linarith)
    · have hq':1≤Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1):=
        (lt_of_not_ge hq).le
      rw [upperSigned_outer hq'] at hpos
      exact (hext _ hq' hpos).trans (by linarith)
  · simp only [upperFlux,ite_eq_right hp,norm_zero]
    exact mul_nonneg κ_pos.le (by linarith)
lemma upperSigned_gradient_cap {x:Space 7} (hq:Cylindrical.radiusSq axis x<1) :
    gradient upperSigned x=gradient smoothCap x := by
  have hc:ContinuousAt (Cylindrical.radiusSq axis) x:=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt
  have he:upperSigned =ᶠ[𝓝 x] smoothCap:=by
    filter_upwards [hc.eventually (gt_mem_nhds hq)] with y hy
    exact upperSigned_cap hy.le
  exact congrArg ((toDual ℝ (Space 7)).symm) he.fderiv_eq
lemma upperSigned_gradient_outer {x:Space 7} (hq:1<Cylindrical.radiusSq axis x) :
    gradient upperSigned x=gradient outerSigned x := by
  have hc:ContinuousAt (Cylindrical.radiusSq axis) x:=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt
  have he:upperSigned =ᶠ[𝓝 x] outerSigned:=by
    filter_upwards [hc.eventually (lt_mem_nhds hq)] with y hy
    exact upperSigned_outer hy.le
  exact congrArg ((toDual ℝ (Space 7)).symm) he.fderiv_eq
lemma upperFlux_eq_calibration {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    upperFlux p=upperCalibration p := by
  rw [upperCalibration_eq hp hq,upperFlux,ite_eq_left hp]
  congr 1
  rcases lt_or_gt_of_ne hq with h|h
  · rw [ite_eq_left h.le,upperSigned_gradient_cap h]
  · rw [ite_eq_right (not_le.mpr h),upperSigned_gradient_outer h]
lemma upperFlux_eventually_eq {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    upperFlux =ᶠ[𝓝 p] upperCalibration := by
  have hn:∀ᶠ z:Space 7×ℝ in 𝓝 p,U z.1<z.2:=
    (U_continuous.continuousAt.comp continuous_fst.continuousAt).eventually_lt
      continuous_snd.continuousAt hp
  have hl:upperParameter p.1 p.2≠0:=(upperParameter_spec hp).1.ne'
  have hc:ContinuousAt (fun z:Space 7×ℝ=>
      Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)) p:=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt.comp
      (((upperParameter_contDiffAt hp hq).continuousAt.inv₀ hl).smul continuous_fst.continuousAt)
  filter_upwards [hn,hc.eventually_ne hq] with z hz hzq
  exact upperFlux_eq_calibration hz hzq
lemma upperFlux_contDiffAt {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    ContDiffAt ℝ ∞ upperFlux p :=
  (upperCalibration_contDiffAt hp hq).congr_of_eventuallyEq (upperFlux_eventually_eq hp hq)
lemma upperParameter_measurable : Measurable (fun z:Space 7×ℝ=>upperParameter z.1 z.2) := by
  let S:Set (Space 7×ℝ):={z|U z.1<z.2}
  have hS:IsOpen S:=isOpen_lt (U_continuous.comp continuous_fst) continuous_snd
  have hh:Measurable (S.piecewise (fun z=>upperParameter z.1 z.2) (fun _=>0)):=
    upperParameter_continuousOn.measurable_piecewise continuousOn_const hS.measurableSet
  convert hh using 1
  ext z
  by_cases hz:U z.1<z.2
  · simp [S,hz]
  · simp [S,hz,upperParameter]
lemma upperFlux_measurable : Measurable upperFlux := by
  have hi:Measurable (fun z:Space 7×ℝ=>(upperParameter z.1 z.2)⁻¹ • z.1):=
    upperParameter_measurable.inv.smul measurable_fst
  have hq:Measurable (fun z:Space 7×ℝ=>Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)):=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.measurable.comp hi
  have h1:MeasurableSet {z:Space 7×ℝ|U z.1<z.2}:=
    measurableSet_lt (U_continuous.measurable.comp measurable_fst) measurable_snd
  have h2:MeasurableSet {z:Space 7×ℝ|Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)≤1}:=
    measurableSet_le hq measurable_const
  exact ((LipschitzSobolev.measurable_gradient.comp hi).ite h2
    (LipschitzSobolev.measurable_gradient.comp hi)).const_smul κ |>.ite h1 measurable_const

/-- The height primitive is integrable and has linear growth, using the actual
field's uniform bound, independently of seam choices. -/
lemma upperFlux_intervalIntegrable (x:Space 7) (a b:ℝ) :
    IntervalIntegrable (fun s:ℝ=>upperFlux (x,s)) MeasureTheory.volume a b := by
  obtain ⟨C,hC,hbound⟩:=upperFlux_uniform_bound
  rw [intervalIntegrable_iff]
  apply MeasureTheory.Integrable.mono' (g:=fun _:ℝ=>C)
    (intervalIntegrable_const (a:=a) (b:=b) (c:=C)).def'
  · exact (upperFlux_measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun s=>hbound (x,s)
end Bernoulli.DeSilvaJerison

end
end

end OAI
