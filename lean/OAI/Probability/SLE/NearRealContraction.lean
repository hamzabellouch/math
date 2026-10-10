import Mathlib
import OAI.Probability.SLE.SwallowExit

namespace OAI

/-! Near Real Contraction for chordal SLE. -/

section
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma reciprocal_real_near_one {z : ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1/2) (hz : ‖z‖ ≤ δ) :
    1 - 2*δ ≤ ((1+z)⁻¹).re := by
  have hl : 1-δ ≤ ‖1+z‖ := by
    have hh := norm_sub_le (1+z) z
    simp only [add_sub_cancel_right, norm_one] at hh
    linarith
  have hn : 0 < ‖1+z‖ := by linarith
  have hne : 1+z ≠ 0 := norm_pos_iff.mp hn
  have he : (1+z)⁻¹ - 1 = -z/(1+z) := by field_simp; ring
  have hb : ‖(1+z)⁻¹ - 1‖ ≤ 2*δ := by
    rw [he,norm_div,norm_neg]
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have hr := Complex.abs_re_le_norm ((1+z)⁻¹-1)
  simp only [sub_re,one_re] at hr
  have := (abs_le.mp (hr.trans hb)).1
  linarith

lemma boundary_difference_coefficient {X δ : ℝ} {D : ℂ}
    (hX : 0 < X) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1/2) (hD : ‖D‖ ≤ δ*X) :
    (-2 / ((X:ℂ)*((X:ℂ)+D))).re ≤ (-2+4*δ)*X⁻¹^2 := by
  have hx : (X:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hz : ‖D/(X:ℂ)‖ ≤ δ := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX]
    exact (div_le_iff₀ hX).mpr hD
  have hh := reciprocal_real_near_one hδ hδ2 hz
  have he : (-2 / ((X:ℂ)*((X:ℂ)+D))) =
      ((-2*X⁻¹^2:ℝ):ℂ)*(1+D/(X:ℂ))⁻¹ := by
    push_cast
    field_simp
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  nlinarith [sq_nonneg X⁻¹]

 

theorem near_real_difference_bound
    (T : ℝ) (hT : 0 ≤ T) (U Q : ℝ → ℝ) (Z : ℝ → ℂ)
    (hU : ContinuousOn U (Icc 0 T)) (hQ : ContinuousOn Q (Icc 0 T))
    (hZ : ContinuousOn Z (Icc 0 T))
    (hpos : ∀ t ∈ Icc 0 T, 0 < Q t-U t)
    (hQd : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q (2/(Q t-U t)) (Icc 0 T) t)
    (hZd : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z (2/(Z t-(U t:ℂ))) (Icc 0 T) t)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1/2)
    (hratio : ∀ t ∈ Icc 0 T, ‖Z t-(Q t:ℂ)‖ ≤ δ*(Q t-U t)) :
    ‖Z T-(Q T:ℂ)‖ ≤ ‖Z 0-(Q 0:ℂ)‖ *
      Real.exp ((-2+4*δ)*(∫ t in (0:ℝ)..T, (Q t-U t)⁻¹^2)) := by
  let X (t : ℝ) := Q t-U t
  let D (t : ℝ) := Z t-(Q t:ℂ)
  have hXc : ContinuousOn X (Icc 0 T) := hQ.sub hU
  have hDc : ContinuousOn D (Icc 0 T) := hZ.sub (Complex.continuous_ofReal.comp_continuousOn hQ)
  have hne (t : ℝ) (ht : t ∈ Icc 0 T) : (X t:ℂ)+D t ≠ 0 := by
    have hl : X t-‖D t‖ ≤ ‖(X t:ℂ)+D t‖ := by
      have hh := norm_sub_le ((X t:ℂ)+D t) (D t)
      simp only [add_sub_cancel_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0 < X t from hpos t ht)] at hh
      linarith
    apply norm_pos_iff.mp
    have hpp := hpos t ht
    have hrr := hratio t ht
    change ‖D t‖ ≤ δ*X t at hrr
    change 0 < X t at hpp
    nlinarith
  let c (t : ℝ) := -2 / ((X t:ℂ)*((X t:ℂ)+D t))
  have hcc : ContinuousOn c (Icc 0 T) := by
    apply continuousOn_const.div
      ((Complex.continuous_ofReal.comp_continuousOn hXc).mul
        ((Complex.continuous_ofReal.comp_continuousOn hXc).add hDc))
    intro t ht
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (hpos t ht).ne') (hne t ht)
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt D (c t*D t) (Icc 0 T) t := by
    have hh := (hZd t ht).sub (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt t (hQd t ht))
    have halg : c t*D t = 2/(Z t-(U t:ℂ)) - ((2/(Q t-U t):ℝ):ℂ) := by
      dsimp only [c,D,X]
      have hxn := Complex.ofReal_ne_zero.mpr (hpos t ht).ne'
      have hzn : Z t-(U t:ℂ) ≠ 0 := by
        convert hne t ht using 1
        simp only [X,D,Complex.ofReal_sub]
        ring
      simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_sub]
      rw [show (Q t:ℂ)-(U t:ℂ)+(Z t-(Q t:ℂ))=Z t-(U t:ℂ) by ring]
      have hx' : (Q t:ℂ)-(U t:ℂ) ≠ 0 := by simpa only [Complex.ofReal_sub] using hxn
      field_simp [hx',hzn]
      ring
    convert hh using 1 <;> try rfl
    exact halg
  have he := complex_linear_ode_exp T hT D c hcc hd
  have hci : IntervalIntegrable (fun t => (c t).re) volume 0 T :=
    (Complex.continuous_re.comp_continuousOn hcc).intervalIntegrable_of_Icc hT
  have hxi : IntervalIntegrable (fun t => (-2+4*δ)*(X t)⁻¹^2) volume 0 T := by
    exact (continuousOn_const.mul ((hXc.inv₀ (fun t ht => (hpos t ht).ne')).pow 2)).intervalIntegrable_of_Icc hT
  have hi : (∫ t in (0:ℝ)..T, (c t).re) ≤
      (-2+4*δ)*(∫ t in (0:ℝ)..T, (X t)⁻¹^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hT hci hxi
    intro t ht
    exact boundary_difference_coefficient (hpos t ht) hδ hδ2 (hratio t ht)
  change ‖D T‖ ≤ _
  have hir : (∫ t in (0:ℝ)..T, (c t).re) = (∫ t in (0:ℝ)..T, c t).re :=
    Complex.reCLM.intervalIntegral_comp_comm (hcc.intervalIntegrable_of_Icc hT)
  rw [he,norm_mul,Complex.norm_exp,← hir]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hi) (norm_nonneg _)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

def BoundaryComparisonFailure (U : ℝ≥0 → ℝ) (x r δ : ℝ) : Prop :=
  ∃ (T : ℝ≥0) (Q Z : ℝ → ℂ), IsPositiveBoundaryClockPath U x T Q ∧
    (∀ t ∈ Icc 0 (T:ℝ), HasDerivWithinAt Z
      (2/(Z t-(U t.toNNReal:ℂ))) (Icc 0 (T:ℝ)) t) ∧
    ‖Z 0-(x:ℂ)‖ ≤ r ∧
    (∀ t ∈ Icc 0 (T:ℝ), ‖Z t-((Q t).re:ℂ)‖ ≤ δ*((Q t).re-U t.toNNReal)) ∧
    δ*((Q T).re-U T) ≤ ‖Z T-((Q T).re:ℂ)‖

lemma BoundaryComparisonFailure.density_crossing
    {U : ℝ≥0 → ℝ} {x r δ β κ : ℝ}
    (hU : Continuous U) (hr : 0 < r) (hδ : 0 < δ) (hδ2 : δ ≤ 1/2) (hβ : 0 < β)
    (hfail : BoundaryComparisonFailure U x r δ)
    (B : ℝ≥0 → ℝ) (heU : ∀ t, U t = Real.sqrt κ*B t) :
    ∃ (T : ℝ≥0) (Q : ℝ → ℂ), IsPositiveBoundaryClockPath U x T Q ∧
      Real.exp (β*Real.log (δ/r)) ≤ boundaryDensity κ (2-4*δ) β (Q T) (B T) := by
  obtain ⟨T,Q,Z,hQ,hZd,hZ0,hratio,hend⟩ := hfail
  have hQd (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : HasDerivWithinAt (fun u => (Q u).re)
      (2/((Q t).re-U t.toNNReal)) (Icc 0 (T:ℝ)) t := by
    simpa only [Function.comp_def,Complex.reCLM_apply,Complex.add_re,Complex.ofReal_re,
      Complex.mul_re,Complex.I_re,mul_zero,Complex.ofReal_im,Complex.I_im,mul_one,
      sub_zero,add_zero] using Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t (hQ.2.2 t ht)
  have hn := near_real_difference_bound (T:ℝ) T.coe_nonneg
    (fun t => U t.toNNReal) (fun t => (Q t).re) Z
    (hU.comp continuous_real_toNNReal).continuousOn
    (Complex.continuous_re.comp_continuousOn hQ.continuousOn)
    (fun t ht => (hZd t ht).continuousWithinAt) hQ.2.1 hQd hZd δ hδ.le hδ2 hratio
  have hc := hQ.clock_identity hU
  have hq0 : ((Q 0).re:ℂ) = (x:ℂ) := by rw [hQ.1,Complex.ofReal_re]
  rw [hq0,← hc] at hn
  have hD : δ*((Q T).re-U T) ≤ r*Real.exp (-(2-4*δ)*(Q T).im) := by
    have hh := hn.trans (mul_le_mul_of_nonneg_right hZ0 (Real.exp_pos _).le)
    rw [show -2+4*δ = -(2-4*δ) by ring] at hh
    exact hend.trans hh
  have hX : 0 < (Q T).re-U T := by simpa only [Real.toNNReal_coe] using hQ.2.1 T ⟨T.coe_nonneg,le_rfl⟩
  have hquot : δ/r ≤ Real.exp (-(2-4*δ)*(Q T).im)/((Q T).re-U T) :=
    (div_le_div_iff₀ hr hX).mpr (by nlinarith [hD])
  have hlog := Real.log_le_log (div_pos hδ hr) hquot
  rw [Real.log_div (Real.exp_pos _).ne' hX.ne',Real.log_exp] at hlog
  refine ⟨T,Q,hQ,?_⟩
  unfold boundaryDensity
  rw [← heU T]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hlog hβ.le]

lemma boundary_density_threshold_initial {κ α β x r δ : ℝ}
    (hx : 0 < x) (hr : 0 < r) (_hδ : 0 < δ) (hβ : 0 ≤ β) (hrx : r ≤ δ*x) :
    boundaryDensity κ α β (x:ℂ) 0 ≤ Real.exp (β*Real.log (δ/r)) := by
  have hq : x⁻¹ ≤ δ/r := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hx hr).mpr
    simpa only [one_mul] using hrx
  have hl := Real.log_le_log (inv_pos.mpr hx) hq
  rw [Real.log_inv] at hl
  simp only [boundaryDensity,Complex.ofReal_im,mul_zero,zero_sub,Complex.ofReal_re,sub_zero]
  exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hl hβ])

lemma boundary_density_threshold_quotient {κ α β x r δ : ℝ}
    (hx : 0 < x) (hr : 0 < r) (hδ : 0 < δ) :
    boundaryDensity κ α β (x:ℂ) 0 / Real.exp (β*Real.log (δ/r)) =
      (r/(δ*x))^β := by
  simp only [boundaryDensity,Complex.ofReal_im,mul_zero,zero_sub,Complex.ofReal_re,sub_zero]
  rw [← Real.exp_sub,Real.rpow_def_of_pos (div_pos hr (mul_pos hδ hx)),
    Real.log_div hr.ne' (mul_pos hδ hx).ne',Real.log_mul hδ.ne' hx.ne',
    Real.log_div hδ.ne' hr.ne']
  congr 1
  ring

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

 
lemma near_real_first_contact {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc 0 T)) (h0 : f 0 < 0) (hTval : 0 ≤ f T) :
    ∃ s ∈ Icc 0 T, f s = 0 ∧ ∀ t ∈ Icc 0 s, f t ≤ 0 := by
  let F (t : ℝ) := f (projIcc 0 T hT t)
  have hFc : Continuous F := hc.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun t => (projIcc 0 T hT t).property)
  have hFe (t : ℝ) (ht : t ∈ Icc 0 T) : F t = f t := by
    simp only [F,projIcc_of_mem hT ht]
  obtain ⟨u,hu,hfu⟩ := intermediate_value_Icc hT hc ⟨h0.le,hTval⟩
  let A := Icc 0 T ∩ F ⁻¹' {0}
  have hAc : IsCompact A := isCompact_Icc.inter_right (isClosed_singleton.preimage hFc)
  have hAn : A.Nonempty := ⟨u,hu,by simpa only [mem_preimage,mem_singleton_iff,hFe u hu] using hfu⟩
  obtain ⟨s,hs,hmin⟩ := hAc.exists_isMinOn hAn continuousOn_id
  have hfs : f s = 0 := (hFe s hs.1).symm.trans hs.2
  refine ⟨s,hs.1,hfs,?_⟩
  intro t ht
  by_contra hn
  have htp : 0 < f t := lt_of_not_ge hn
  have hsub : Icc 0 t ⊆ Icc 0 T := fun v hv => ⟨hv.1,hv.2.trans (ht.2.trans hs.1.2)⟩
  obtain ⟨v,hv,hfv⟩ := intermediate_value_Icc ht.1 (hc.mono hsub) ⟨h0.le,htp.le⟩
  have hvA : v ∈ A := ⟨hsub hv,by simpa only [mem_preimage,mem_singleton_iff,hFe v (hsub hv)] using hfv⟩
  have hst : s ≤ t := (hmin hvA).trans hv.2
  have hts : t = s := le_antisymm ht.2 hst
  exact htp.ne' (hts ▸ hfs)

lemma rightField_im (a u : ℝ) (z : ℂ) :
    (rightField a u z).im = (-2 / Complex.normSq (rightCenter a u z))*z.im := by
  simp only [rightField,Complex.mul_im,Complex.re_ofNat,Complex.im_ofNat,
    zero_mul,add_zero,Complex.inv_im]
  have him : (rightCenter a u z).im = z.im := by simp [rightCenter]
  rw [him]
  ring

 

lemma right_flow_im_pos {U : ℝ → ℝ} (hU : Continuous U) {a : ℝ} (ha : 0 < a)
    {Z : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z
      (rightField a (U t) (Z t)) (Icc 0 T) t)
    (h0 : 0 < (Z 0).im) : 0 < (Z T).im := by
  have hZc : ContinuousOn Z (Icc 0 T) := fun t ht => (hd t ht).continuousWithinAt
  let c (t : ℝ) := -2 / Complex.normSq (rightCenter a (U t) (Z t))
  have hcenter : ContinuousOn (fun t => rightCenter a (U t) (Z t)) (Icc 0 T) := by
    unfold rightCenter
    fun_prop
  have hcc : ContinuousOn c (Icc 0 T) :=
    continuousOn_const.div (Complex.continuous_normSq.comp_continuousOn hcenter)
      (fun t ht => (Complex.normSq_pos.mpr (rightCenter_ne_zero ha _ _)).ne')
  have hfd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt
      (fun s => ((Z s).im:ℂ)) ((c t:ℂ)*((Z t).im:ℂ)) (Icc 0 T) t := by
    have hh := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt t
      (Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t (hd t ht))
    simpa only [Function.comp_def,Complex.ofRealCLM_apply,Complex.imCLM_apply,
      rightField_im,Complex.ofReal_mul,c] using hh
  have he := complex_linear_ode_exp T hT (fun t => ((Z t).im:ℂ)) (fun t => (c t:ℂ))
    (Complex.continuous_ofReal.comp_continuousOn hcc) hfd
  have hint : (∫ t in (0:ℝ)..T, (c t:ℂ)) = ((∫ t in (0:ℝ)..T, c t : ℝ):ℂ) := by
    exact Complex.ofRealCLM.intervalIntegral_comp_comm (hcc.intervalIntegrable_of_Icc hT)
  rw [hint,← Complex.ofReal_exp,← Complex.ofReal_mul] at he
  have heR : (Z T).im = (Z 0).im * Real.exp (∫ t in (0:ℝ)..T, c t) := Complex.ofReal_injective he
  rw [heR]
  exact mul_pos h0 (Real.exp_pos _)

lemma right_flow_unclipped_of_ratio {a δ X u q : ℝ} {z : ℂ}
    (haX : a ≤ X) (hX : 0 ≤ X) (hδ : δ ≤ 1/2)
    (hXeq : X = q-u) (hratio : ‖z-(q:ℂ)‖ ≤ δ*X) :
    a/2 ≤ z.re-u := by
  have hn : q-z.re ≤ ‖z-(q:ℂ)‖ := by
    have hh := Complex.re_le_norm (-(z-(q:ℂ)))
    simpa only [Complex.neg_re,Complex.sub_re,Complex.ofReal_re,neg_sub,norm_neg,norm_sub_rev] using hh
  have hmul := mul_le_mul_of_nonneg_right hδ hX
  nlinarith

 

lemma no_boundary_failure_gives_complex_flow
    {U : ℝ≥0 → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {x r δ : ℝ} (hrx : r < δ*x) (hδ2 : δ ≤ 1/2)
    (hno : ¬ BoundaryComparisonFailure U x r δ)
    {T : ℝ≥0} {Q : ℝ → ℂ} (hQ : IsPositiveBoundaryClockPath U x T Q)
    (w : ℂ) (hw : ‖w-(x:ℂ)‖ ≤ r) :
    ∃ Z : ℝ → ℂ, Z 0 = w ∧
      (∀ t ∈ Icc 0 (T:ℝ), HasDerivWithinAt Z
        (2/(Z t-(U t.toNNReal:ℂ))) (Icc 0 (T:ℝ)) t) ∧
      (∀ t ∈ Icc 0 (T:ℝ), ‖Z t-((Q t).re:ℂ)‖ < δ*((Q t).re-U t.toNNReal)) := by
  obtain ⟨a,ha,hgap⟩ := hQ.positive_lower_bound hU
  have hUc : Continuous (fun t : ℝ => U t.toNNReal) := hU.comp continuous_real_toNNReal
  obtain ⟨Y,hYm,hY0,hYd⟩ := exists_measurable_right_flow
    (fun t (_ : Unit) => U t.toNNReal)
    (hUc.measurable.comp measurable_fst) (fun _ => hUc)
    (fun _ => w) measurable_const (half_pos ha)
  let Z (t : ℝ) := Y t ()
  have hZ0 : Z 0 = w := hY0 ()
  have hZd (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt Z
      (rightField (a/2) (U t.toNNReal) (Z t)) (Ici 0) t := hYd () t ht
  have hZc : ContinuousOn Z (Icc 0 (T:ℝ)) :=
    fun t ht => ((hZd t ht.1).mono (fun s hs => hs.1)).continuousWithinAt
  let f (t : ℝ) := ‖Z t-((Q t).re:ℂ)‖-δ*((Q t).re-U t.toNNReal)
  have hfc : ContinuousOn f (Icc 0 (T:ℝ)) := by
    exact (hZc.sub (Complex.continuous_ofReal.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn hQ.continuousOn))).norm.sub
      (continuousOn_const.mul ((Complex.continuous_re.comp_continuousOn hQ.continuousOn).sub hUc.continuousOn))
  have hf0 : f 0 < 0 := by
    dsimp only [f]
    rw [hZ0,hQ.1,Complex.ofReal_re,Real.toNNReal_zero,hU0,sub_zero]
    linarith
  have hratio (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : f t < 0 := by
    by_contra hn
    have hsub : Icc 0 t ⊆ Icc 0 (T:ℝ) := fun s hs => ⟨hs.1,hs.2.trans ht.2⟩
    obtain ⟨s,hs,hfs,hbefore⟩ := near_real_first_contact ht.1 (hfc.mono hsub) hf0 (le_of_not_gt hn)
    let S : ℝ≥0 := ⟨s,hs.1⟩
    have hsubS : Icc 0 (S:ℝ) ⊆ Icc 0 (T:ℝ) := fun v hv => ⟨hv.1,hv.2.trans (hs.2.trans ht.2)⟩
    have hcomp (v : ℝ) (hv : v ∈ Icc 0 (S:ℝ)) :
        ‖Z v-((Q v).re:ℂ)‖ ≤ δ*((Q v).re-U v.toNNReal) := sub_nonpos.mp (hbefore v hv)
    have hreal (v : ℝ) (hv : v ∈ Icc 0 (S:ℝ)) : a/2 ≤ (Z v).re-U v.toNNReal :=
      right_flow_unclipped_of_ratio (hgap v (hsubS hv)) (hQ.2.1 v (hsubS hv)).le hδ2 rfl (hcomp v hv)
    apply hno
    refine ⟨S,Q,Z,⟨hQ.1,fun v hv => hQ.2.1 v (hsubS hv),
      fun v hv => (hQ.2.2 v (hsubS hv)).mono hsubS⟩,?_,?_,hcomp,?_⟩
    · intro v hv
      rw [← rightField_eq (hreal v hv)]
      exact (hZd v hv.1).mono (fun u hu => hu.1)
    · simpa only [hZ0] using hw
    · have hh : ‖Z s-((Q s).re:ℂ)‖ = δ*((Q s).re-U s.toNNReal) := sub_eq_zero.mp hfs
      have hS : s.toNNReal = S := by
        apply NNReal.eq
        exact Real.coe_toNNReal s hs.1
      change δ*((Q s).re-U S) ≤ ‖Z s-((Q s).re:ℂ)‖
      rw [← hS]
      exact hh.ge
  have hreal (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : a/2 ≤ (Z t).re-U t.toNNReal :=
    right_flow_unclipped_of_ratio (hgap t ht) (hQ.2.1 t ht).le hδ2 rfl (sub_neg.mp (hratio t ht)).le
  refine ⟨Z,hZ0,?_,fun t ht => sub_neg.mp (hratio t ht)⟩
  intro t ht
  rw [← rightField_eq (hreal t ht)]
  exact (hZd t ht.1).mono (fun s hs => hs.1)

 

theorem IsCapacityTwoWitness.half_ball_survives_before_boundary_collision
    {U : ℝ≥0 → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ} (h : IsCapacityTwoWitness U γ G F)
    {x r δ : ℝ} (hrx : r < δ*x) (hδ2 : δ ≤ 1/2)
    (hno : ¬ BoundaryComparisonFailure U x r δ)
    {T : ℝ≥0} {Q : ℝ → ℂ} (hQ : IsPositiveBoundaryClockPath U x T Q) :
    ∀ w : ℂ, 0 < w.im → ‖w-(x:ℂ)‖ ≤ r →
      w ∈ survivingDomain γ T ∧
      ‖G T w-((Q T).re:ℂ)‖ < δ*((Q T).re-U T) := by
  intro w hwp hw
  obtain ⟨Z,hZ0,hZd,hratio⟩ := no_boundary_failure_gives_complex_flow hU hU0 hrx hδ2 hno hQ w hw
  obtain ⟨a,ha,hgap⟩ := hQ.positive_lower_bound hU
  have hclip (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : a/2 ≤ (Z t).re-U t.toNNReal :=
    right_flow_unclipped_of_ratio (hgap t ht) (hQ.2.1 t ht).le hδ2 rfl (hratio t ht).le
  have hZp (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : 0 < (Z t).im := by
    have hsub : Icc 0 t ⊆ Icc 0 (T:ℝ) := fun s hs => ⟨hs.1,hs.2.trans ht.2⟩
    apply right_flow_im_pos (hU.comp continuous_real_toNNReal) (half_pos ha) ht.1
    · intro s hs
      dsimp only [Function.comp_def]
      rw [rightField_eq (hclip s (hsub hs))]
      exact (hZd s (hsub hs)).mono hsub
    · simpa only [hZ0] using hwp
  obtain ⟨hlive,he⟩ := h.forward_flow_survives T Z hZp hZd
  rw [hZ0] at hlive he
  refine ⟨hlive,?_⟩
  rw [he]
  simpa only [Real.toNNReal_coe] using hratio T ⟨T.coe_nonneg,le_rfl⟩

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma upper_mobius_norm_lt_one {v w : ℂ} (hv : 0 < v.im) (hw : 0 < w.im) :
    ‖(v - w) / (v - star w)‖ < 1 := by
  have hd : v - star w ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at hh
    linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  have he : ‖v - w‖ ^ 2 < ‖v - star w‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    nlinarith [mul_pos hv hw]
  nlinarith [norm_nonneg (v - w), norm_nonneg (v - star w)]

 

lemma radius_of_halfplane_map {f : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball z r))
    (hm : MapsTo f (ball z r) upperHalfPlane) (hf : deriv f z ≠ 0) :
    r ≤ 2 * (f z).im / ‖deriv f z‖ := by
  have hz : z ∈ ball z r := mem_ball_self hr
  have hy : 0 < (f z).im := hm hz
  have hden (w : ℂ) (hw : w ∈ ball z r) : f w - star (f z) ≠ 0 := by
    intro he
    have hx := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at hx
    have hwyo : 0 < (f w).im := hm hw
    linarith
  let g := fun w => (f w - f z) / (f w - star (f z))
  have hg0 : g z = 0 := by dsimp [g]; rw [sub_self, zero_div]
  have hgd : DifferentiableOn ℂ g (ball z r) :=
    (hd.sub_const _).div (hd.sub_const _) hden
  have hgm : MapsTo g (ball z r) (closedBall (g z) 1) := by
    intro w hw
    rw [hg0, mem_closedBall_zero_iff]
    exact (upper_mobius_norm_lt_one (hm hw) hy).le
  have hdz : HasDerivAt f (deriv f z) z := (hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hgg : deriv g z = deriv f z / (f z - star (f z)) := by
    calc
      deriv g z = (deriv f z * (f z - star (f z)) - (f z - f z) * deriv f z) /
          (f z - star (f z)) ^ 2 :=
        ((hdz.sub_const (f z)).div (hdz.sub_const (star (f z))) (hden z hz)).deriv
      _ = _ := by
        rw [sub_self, zero_mul, sub_zero, pow_two, mul_div_mul_right _ _ (hden z hz)]
  have hn : ‖f z - star (f z)‖ = 2 * (f z).im := by
    rw [Complex.star_def, Complex.sub_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hy), Complex.norm_I, mul_one]
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball hgd hgm hr
  rw [hgg, norm_div, hn] at hh
  have hn' := norm_pos_iff.mpr hf
  apply (le_div_iff₀ hn').mpr
  have hq := (div_le_div_iff₀ (mul_pos (by norm_num) hy) hr).mp hh
  nlinarith

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma ball_subset_survivingDomain {γ : ℝ≥0 → ℂ} {t : ℝ≥0} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hz : z ∈ survivingDomain γ t)
    (hfree : ball z r ⊆ upperHalfPlane \ (γ '' Icc 0 t)) :
    ball z r ⊆ survivingDomain γ t := by
  have hcc := (convex_ball z r).isPreconnected.subset_connectedComponentIn (mem_ball_self hr) hfree
  intro w hw
  refine ⟨hfree hw, ?_⟩
  rw [← connectedComponentIn_eq (hcc hw)]
  exact hz.2

lemma ball_subset_upperHalfPlane {z : ℂ} {r : ℝ} (hr : r ≤ z.im) :
    ball z r ⊆ upperHalfPlane := by
  intro w hw
  have hh : ‖w - z‖ < r := mem_ball_iff_norm.mp hw
  have hi := Complex.abs_im_le_norm (w - z)
  simp only [Complex.sub_im] at hi
  change 0 < w.im
  have hx := neg_le_abs (w.im - z.im)
  linarith

 

lemma IsCapacityTwoWitness.trace_approach_of_radius_lt
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t) (r : ℝ)
    (hr : 0 < r) (hy : r ≤ z.im) (hR : fullRadius G t z < r) :
    ∃ s ∈ Icc 0 t, dist (γ s) z < r := by
  by_contra hn
  have hn' (s : ℝ≥0) (hs : s ∈ Icc 0 t) : r ≤ dist (γ s) z :=
    le_of_not_gt (fun he => hn ⟨s, hs, he⟩)
  have hfree : ball z r ⊆ upperHalfPlane \ (γ '' Icc 0 t) := by
    intro w hw
    refine ⟨ball_subset_upperHalfPlane hy hw, ?_⟩
    rintro ⟨s, hs, rfl⟩
    exact not_lt_of_ge (hn' s hs) (mem_ball.mp hw)
  have hb := ball_subset_survivingDomain hr hz hfree
  have hd : DifferentiableOn ℂ (G t) (ball z r) := (h.2.2.2.1 t).mono hb
  have hm : MapsTo (G t) (ball z r) upperHalfPlane := fun w hw => h.2.2.2.2.2.1 t (hb hw)
  have hf : deriv (G t) z ≠ 0 := norm_pos_iff.mp (h.derivative_norm_positive hU t z hz)
  exact not_lt_of_ge (radius_of_halfplane_map hr hd hm hf) hR

end SLEExactGauge
end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma IsCapacityTwoWitness.trace_mem_closure_surviving
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (s t : ℝ≥0) (hst : s ≤ t) :
    γ t ∈ closure (survivingDomain γ s) := by
  have hfmap := h.2.2.2.2.2.2.1 t
  have htip := h.2.2.2.2.2.2.2.2.2.2.2.2 t
  apply mem_closure_of_tendsto htip
  filter_upwards [self_mem_nhdsWithin] with y hy
  apply survivingDomain_antitone γ hst
  apply hfmap
  change 0 < (((U t : ℝ) : ℂ) + (y : ℂ) * Complex.I).im
  simpa using hy

lemma IsCapacityTwoWitness.surviving_of_free_ball_future_tip
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (s t : ℝ≥0) (hst : s ≤ t)
    (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hfree : ball z r ⊆ upperHalfPlane \ (γ '' Icc 0 s))
    (htip : γ t ∈ ball z r) : z ∈ survivingDomain γ s := by
  obtain ⟨w, hwb, hw⟩ := mem_closure_iff.mp (h.trace_mem_closure_surviving s t hst)
    (ball z r) isOpen_ball htip
  have hcc := (convex_ball z r).isPreconnected.subset_connectedComponentIn (mem_ball_self hr) hfree
  refine ⟨hfree (mem_ball_self hr), ?_⟩
  rw [connectedComponentIn_eq (hcc hwb)]
  exact hw.2

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex Metric
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma IsCapacityTwoWitness.boundary_path_of_half_ball_survivor
    {U : ℝ≥0 → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ} (h : IsCapacityTwoWitness U γ G F)
    {x r δ : ℝ} (hx : 0 < x) (hrx : r < δ*x) (hδ2 : δ ≤ 1/2)
    (hno : ¬ BoundaryComparisonFailure U x r δ)
    (T : ℝ≥0) (w : ℂ) (hw : ‖w-(x:ℂ)‖ ≤ r)
    (hlive : w ∈ survivingDomain γ T) :
    ∃ Q : ℝ → ℂ, IsPositiveBoundaryClockPath U x T Q := by
  let a := min (x/2) (G T w).im
  have hy : 0 < (G T w).im := h.imag_positive T w hlive
  have ha : 0 < a := lt_min (half_pos hx) hy
  have hax : a < x := (min_le_left _ _).trans_lt (half_lt_self hx)
  have hay : a ≤ (G T w).im := min_le_right _ _
  obtain ⟨L,Y,hYm,hYl,hY0,hYd,hYa⟩ := boundary_clock_global_adapted_solution
    (fun t (_ : Unit) => U t) (hU.measurable.comp measurable_fst) (fun _ => hU)
    1 a ha (x:ℂ)
  let Q (t : ℝ) := Y t ()
  have hQ0 : Q 0 = (x:ℂ) := hY0 ()
  have hQd (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt Q
      (boundaryClockField a (U t.toNNReal) (Q t)) (Ici 0) t := by
    simpa only [Real.sqrt_one,one_mul] using hYd () t ht
  have hQc : Continuous Q := (hYl ()).continuous
  let f (t : ℝ) := a-((Q t).re-U t.toNNReal)
  have hfc : Continuous f := continuous_const.sub
    ((Complex.continuous_re.comp hQc).sub (hU.comp continuous_real_toNNReal))
  have hf0 : f 0 < 0 := by
    dsimp only [f]
    rw [hQ0,Complex.ofReal_re,Real.toNNReal_zero,hU0,sub_zero]
    exact sub_neg.mpr hax
  have hgap (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : a < (Q t).re-U t.toNNReal := by
    by_contra hn
    obtain ⟨s,hs,hfs,hbefore⟩ := near_real_first_contact ht.1 hfc.continuousOn hf0
      (sub_nonneg.mpr (le_of_not_gt hn))
    let S : ℝ≥0 := ⟨s,hs.1⟩
    have hS : s.toNNReal = S := by apply NNReal.eq; exact Real.coe_toNNReal s hs.1
    have hST : S ≤ T := hs.2.trans ht.2
    have hgapS (v : ℝ) (hv : v ∈ Icc 0 (S:ℝ)) : a ≤ (Q v).re-U v.toNNReal :=
      sub_nonpos.mp (hbefore v hv)
    have hpath : IsPositiveBoundaryClockPath U x S Q := by
      refine ⟨hQ0,fun v hv => ha.trans_le (hgapS v hv),?_⟩
      intro v hv
      simpa only [boundaryClockField,positiveBoundaryField_eq (hgapS v hv),max_eq_right (hgapS v hv)] using
        (hQd v hv.1).mono (show Icc (0:ℝ) (S:ℝ) ⊆ Ici 0 from fun u hu => hu.1)
    have hratio := (h.half_ball_survives_before_boundary_collision hU hU0 hrx hδ2 hno hpath
      w hlive.1.1 hw).2
    have hgapEq : (Q S).re-U S = a := by
      change (Q s).re-U S = a
      rw [← hS]
      exact (sub_eq_zero.mp hfs).symm
    rw [hgapEq] at hratio
    have him : (G S w).im ≤ ‖G S w-((Q S).re:ℂ)‖ := by
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using
        Complex.im_le_norm (G S w-((Q S).re:ℂ))
    have hmono : (G T w).im ≤ (G S w).im := by
      have hh := h.imag_antitoneOn T w hlive ⟨S.coe_nonneg,hST⟩ ⟨T.coe_nonneg,le_rfl⟩ hST
      simpa only [Real.toNNReal_coe] using hh
    have hδa : δ*a ≤ a/2 := by nlinarith [mul_le_mul_of_nonneg_right hδ2 ha.le]
    linarith
  refine ⟨Q,hQ0,fun t ht => ha.trans (hgap t ht),?_⟩
  intro t ht
  simpa only [boundaryClockField,positiveBoundaryField_eq (hgap t ht).le,max_eq_right (hgap t ht).le] using
    (hQd t ht.1).mono (show Icc (0:ℝ) (T:ℝ) ⊆ Ici 0 from fun s hs => hs.1)

lemma IsCapacityTwoWitness.tip_avoids_half_ball_of_boundary_path
    {U : ℝ≥0 → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ} (h : IsCapacityTwoWitness U γ G F)
    {x r δ : ℝ} (hrx : r < δ*x) (hδ2 : δ ≤ 1/2)
    (hno : ¬ BoundaryComparisonFailure U x r δ)
    {T : ℝ≥0} {Q : ℝ → ℂ} (hQ : IsPositiveBoundaryClockPath U x T Q) :
    r ≤ ‖γ T-(x:ℂ)‖ := by
  by_contra hn
  have hnear : ∀ᶠ y : ℝ in 𝓝[>] 0,
      ‖F T ((U T:ℂ)+(y:ℂ)*I)-(x:ℂ)‖ < r := by
    apply (tendsto_order.1 ((h.2.2.2.2.2.2.2.2.2.2.2.2 T).sub tendsto_const_nhds).norm).2
    exact lt_of_not_ge hn
  obtain ⟨y,hynear,hy⟩ := (hnear.and (show ∀ᶠ y : ℝ in 𝓝[>] 0, 0 < y from self_mem_nhdsWithin)).exists
  have hupper : (U T:ℂ)+(y:ℂ)*I ∈ upperHalfPlane := by
    change 0 < ((U T:ℂ)+(y:ℂ)*I).im
    simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,mul_one,Complex.I_re,mul_zero,add_zero,zero_add] using hy
  have hlive := h.2.2.2.2.2.2.1 T hupper
  have hratio := (h.half_ball_survives_before_boundary_collision hU hU0 hrx hδ2 hno hQ
    _ hlive.1.1 hynear.le).2
  have hg := h.2.2.2.2.2.2.2.2.1 T _ hupper
  rw [hg] at hratio
  have hX : 0 < (Q T).re-U T := by
    simpa only [Real.toNNReal_coe] using hQ.2.1 T ⟨T.coe_nonneg,le_rfl⟩
  have hmargin := right_flow_unclipped_of_ratio (a := (Q T).re-U T) le_rfl hX.le hδ2 rfl hratio.le
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,mul_zero,
    Complex.ofReal_im,Complex.I_im,zero_mul,add_zero,sub_self] at hmargin
  linarith

 

theorem IsCapacityTwoWitness.all_time_real_center_avoidance
    {U : ℝ≥0 → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ} (h : IsCapacityTwoWitness U γ G F)
    {x r δ : ℝ} (hx : 0 < x) (hrx : r < δ*x) (hδ2 : δ ≤ 1/2)
    (hno : ¬ BoundaryComparisonFailure U x r δ) :
    ∀ T : ℝ≥0, r ≤ ‖γ T-(x:ℂ)‖ := by
  intro T
  by_contra hn
  have htip : γ T ∈ ball (x:ℂ) r := by
    rw [mem_ball,dist_eq_norm]
    exact lt_of_not_ge hn
  obtain ⟨w,hwb,hw⟩ := mem_closure_iff.mp (h.trace_mem_closure_surviving T T le_rfl)
    (ball (x:ℂ) r) isOpen_ball htip
  have hwn : ‖w-(x:ℂ)‖ ≤ r := (by simpa only [mem_ball,dist_eq_norm] using hwb : ‖w-(x:ℂ)‖ < r).le
  obtain ⟨Q,hQ⟩ := h.boundary_path_of_half_ball_survivor hU hU0 hx hrx hδ2 hno T w hwn hw
  exact hn (h.tip_avoids_half_ball_of_boundary_path hU hU0 hrx hδ2 hno hQ)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma boundary_comparison_failure_probability_regular
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ β x r δ : ℝ) (hκ : 0 < κ) (hx : 0 < x) (hr : 0 < r)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1/2) (hβ : 0 < β)
    (heq : -(2-4*δ)-2+κ*(β+1)/2=0) :
    P {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r δ} ≤
      ENNReal.ofReal ((r/(δ*x))^β) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  by_cases hrx : r ≤ δ*x
  · have hprob := boundary_maximal_density hB κ (2-4*δ) β x
      (Real.exp (β*Real.log (δ/r))) hκ hx (Real.exp_pos _) heq
        (boundary_density_threshold_initial hx hr hδ hβ.le hrx)
    rw [boundary_density_threshold_quotient hx hr hδ] at hprob
    apply (measure_mono (show {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r δ} ⊆
      {ω | ∃ (T : ℝ≥0) (Q : ℝ → ℂ), IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*B t ω) x T Q ∧
        Real.exp (β*Real.log (δ/r)) ≤ boundaryDensity κ (2-4*δ) β (Q T) (B T ω)} from ?_)).trans hprob
    intro ω hω
    exact hω.density_crossing ((hBc ω).const_mul _) hr hδ hδ2 hβ (fun t => B t ω) (fun t => rfl)
  · have hq : 1 ≤ r/(δ*x) := (le_div_iff₀ (mul_pos hδ hx)).mpr (by linarith)
    have hp := Real.one_le_rpow hq hβ.le
    exact prob_le_one.trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)

 

theorem boundary_comparison_failure_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ β x r δ : ℝ) (hκ : 0 < κ) (hx : 0 < x) (hr : 0 < r)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1/2) (hβ : 0 < β)
    (heq : -(2-4*δ)-2+κ*(β+1)/2=0) :
    P {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r δ} ≤
      ENNReal.ofReal ((r/(δ*x))^β) := by
  obtain ⟨C,hCm,hCc,hC0,hC,hCB⟩ := exists_regular_brownian_version hB
  apply (measure_mono_ae (show {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r δ} ≤ᵐ[P]
      {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*C t ω) x r δ} from ?_)).trans
      (boundary_comparison_failure_probability_regular hC hCc κ β x r δ hκ hx hr hδ hδ2 hβ heq)
  filter_upwards [hCB] with ω he
  intro h
  change BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r δ at h
  simpa only [he] using h

 
theorem boundary_comparison_failure_sle_exponent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ x r : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) (hx : 0 < x) (hr : 0 < r) :
    P {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r ((8-κ)/32)} ≤
      ENNReal.ofReal ((r/(((8-κ)/32)*x))^(3*(8-κ)/(4*κ))) := by
  apply boundary_comparison_failure_probability hB κ _ x r _ hκ hx hr
  · positivity
  · linarith
  · positivity
  · field_simp
    ring

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 m} {τ : Ω → ℝ≥0}

 

lemma stopping_grid_piece_measurable
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (n k : ℕ) :
    MeasurableSet[ℱ (stopGridTime n k)] (A ∩ {ω | stopGridIndex n (τ ω) = k}) := by
  have hle (j : ℕ) : MeasurableSet[ℱ (stopGridTime n j)]
      (A ∩ {ω | stopGridIndex n (τ ω) ≤ j}) := by
    simpa only [stopGridIndex_le, WithTop.coe_le_coe] using hA.2 (stopGridTime n j)
  cases k with
  | zero => simpa only [Nat.le_zero] using hle 0
  | succ k =>
    have he : A ∩ {ω | stopGridIndex n (τ ω) = k + 1} =
        (A ∩ {ω | stopGridIndex n (τ ω) ≤ k + 1}) \ (A ∩ {ω | stopGridIndex n (τ ω) ≤ k}) := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff]
      constructor
      · rintro ⟨hω, heq⟩
        exact ⟨⟨hω, heq.le⟩, fun hb => by omega⟩
      · rintro ⟨⟨hω, hle⟩, hn⟩
        exact ⟨hω, by have hh : ¬ stopGridIndex n (τ ω) ≤ k := fun hk => hn ⟨hω, hk⟩; omega⟩
    rw [he]
    exact (hle (k + 1)).diff (ℱ.mono (monotone_stopGridTime n (Nat.le_succ k)) _ (hle k))

omit m in
lemma grid_partition_union (A : Set Ω) (n : ℕ) :
    (⋃ k : ℕ, A ∩ {ω | stopGridIndex n (τ ω) = k}) = A := by
  ext ω
  simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
  exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

omit m in
lemma grid_partition_disjoint (A : Set Ω) (n : ℕ) :
    Pairwise (fun i j : ℕ => Disjoint (A ∩ {ω | stopGridIndex n (τ ω) = i}) (A ∩ {ω | stopGridIndex n (τ ω) = j})) := by
  intro i j hij
  apply disjoint_left.mpr
  intro ω hi hj
  exact hij (hi.2.symm.trans hj.2)

 

lemma integral_stopping_grid_glue [IsFiniteMeasure P]
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (n : ℕ)
    (f : Ω → ℝ) (hf : Integrable f P) (c : ℝ)
    (hpiece : ∀ k : ℕ, (∫ ω in A ∩ {ω | stopGridIndex n (τ ω) = k}, f ω ∂P) =
      P.real (A ∩ {ω | stopGridIndex n (τ ω) = k}) * c) :
    (∫ ω in A, f ω ∂P) = P.real A * c := by
  have hm (k : ℕ) : MeasurableSet (A ∩ {ω | stopGridIndex n (τ ω) = k}) :=
    ℱ.le _ _ (stopping_grid_piece_measurable hτ hA n k)
  have hfSum := hasSum_integral_iUnion hm (grid_partition_disjoint (τ := τ) A n) hf.integrableOn
  have hconstSum := hasSum_integral_iUnion hm (grid_partition_disjoint (τ := τ) A n)
    (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P).integrableOn
  simp only [grid_partition_union, hpiece] at hfSum
  simp only [grid_partition_union, integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ] at hconstSum
  exact HasSum.unique hfSum (hconstSum.mul_right c)

end SLEExactGauge
end

 
end

end OAI
