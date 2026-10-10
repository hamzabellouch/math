import Mathlib
import OAI.Probability.SLELocalization.LoewnerExit
import OAI.Probability.SLE.ClippedCoordinates

namespace OAI


/-! Conformal localization and Finite Clock estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.FiniteClock

lemma live_density_below {κ : ℝ} (hκ : 0 < κ ∧ κ < 8)
    {B : ℝ≥0 → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal) γ g f)
    (hc : Continuous B) {z : ℂ} {s u δ : ℝ}
    (hs : 0 ≤ s) (hz : z ∈ localizationDomain γ s)
    (hclock : Real.log (2*z.im)-Real.log (loewnerRadius g s z) = u)
    (hangle : loewnerAngleSine κ B g s z < angleFloor δ u) :
    finiteStoppedDensity κ B γ g z u ∈ Ioo 0 (threshold κ z δ u) := by
  have hU : ContinuousOn (fun t : ℝ => Real.sqrt κ*B t.toNNReal) (Ici 0) := (continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn
  have hy : 0 < z.im := hz.1.1
  have hr := hm.radius_pos hs hz
  have hrad : loewnerRadius g s z = (2*z.im)*Real.exp (-u) := by
    have he : Real.log (loewnerRadius g s z) = Real.log (2*z.im)+(-u) := by linarith
    have hh := congrArg Real.exp he
    simpa only [Real.exp_log hr,Real.exp_add,Real.exp_log (show 0<2*z.im by positivity)] using hh
  have hstop := hm.firstLiveRadiusStop_eq hU (t := ⟨s,hs⟩) hz hrad
  have hsin : 0 < loewnerAngleSine κ B g s z := by
    apply div_pos (hm.im_pos hs hz)
    simpa only [Complex.ofReal_mul] using (norm_pos_iff.2 (hm.centered_ne_zero hs hz))
  have hRp := Real.rpow_pos_of_pos hr (-codimension κ)
  have hval : 0 < (loewnerRadius g s z)^(-codimension κ)*(loewnerAngleSine κ B g s z)^(8/κ-1) :=
    mul_pos hRp (Real.rpow_pos_of_pos hsin _)
  have hlt : (loewnerRadius g s z)^(-codimension κ)*(loewnerAngleSine κ B g s z)^(8/κ-1) <
      ((2*z.im)*Real.exp (-u))^(-codimension κ)*(angleFloor δ u)^(8/κ-1) := by
    rw [← hrad]
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hsin.le hangle (exponent_pos hκ)) hRp
  simp only [finiteStoppedDensity,hstop]
  exact ⟨ENNReal.ofReal_pos.2 hval,ENNReal.ofReal_lt_ofReal_iff (hval.trans hlt) |>.2 hlt⟩

lemma exponential_clock_bound {T δ Y₀ : ℝ} {Y C Q : ℝ → ℝ}
    (hT : 0 ≤ T) (hδ : 0 < δ) (hY₀ : 0 < Y₀)
    (hYinit : Y 0 = Y₀) (hCinit : C 0 = 0)
    (hY : ContinuousOn Y (Icc 0 T)) (hC : ContinuousOn C (Icc 0 T))
    (_hYpos : ∀ t ∈ Icc 0 T, 0 < Y t)
    (hQpos : ∀ t ∈ Ioo 0 T, 0 < Q t)
    (hYQ : ∀ t ∈ Ioo 0 T, (Y t)^2 ≤ Q t)
    (hangle : ∀ t ∈ Ioo 0 T, (angleFloor δ (C t))^2 * Q t ≤ (Y t)^2)
    (hdY : ∀ t ∈ Ioo 0 T, HasDerivAt Y (-2*Y t/Q t) t)
    (hdC : ∀ t ∈ Ioo 0 T, HasDerivAt C (4*(Y t)^2/(Q t)^2) t) :
    T ≤ Y₀^2/(2*δ^4) := by
  have hh : AntitoneOn (fun t => (Y t)^2 * Real.exp (C t)) (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      ((hY.pow 2).mul (Real.continuous_exp.comp_continuousOn hC))
      (f' := fun t => (2*Y t*(-2*Y t/Q t))*Real.exp (C t) +
        (Y t)^2*(Real.exp (C t)*(4*(Y t)^2/(Q t)^2)))
    · intro t ht
      rw [interior_Icc] at ht
      convert (((hdY t ht).pow 2).mul (hdC t ht).exp).hasDerivWithinAt
        (s := interior (Icc 0 T)) using 1 <;> first | rfl | (simp only [Pi.pow_apply]; ring)
    · intro t ht
      rw [interior_Icc] at ht
      have hq := hQpos t ht
      apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hq)).1
      have hd := hYQ t ht
      have hb := mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ 4*(Y t)^2*Real.exp (C t) by positivity) (sub_nonpos.2 hd)
      field_simp
      nlinarith [hb]
  have height (t : ℝ) (ht : t ∈ Icc 0 T) :
      (Y t)^2 ≤ Y₀^2*(Real.exp (-C t/2))^2 := by
    have hh' := hh ⟨le_rfl,hT⟩ ht ht.1
    simp only [hYinit,hCinit,Real.exp_zero,mul_one] at hh'
    have he : Real.exp (C t)*(Real.exp (-C t/2))^2 = 1 := by
      rw [pow_two,← Real.exp_add,← Real.exp_add]
      convert Real.exp_zero using 1; congr 1; ring
    have hb := mul_le_mul_of_nonneg_right hh' (sq_nonneg (Real.exp (-C t/2)))
    rwa [mul_assoc,he,mul_one] at hb
  have rate (t : ℝ) (ht : t ∈ Ioo 0 T) :
      2*δ^4/Y₀^2 ≤ (4*(Y t)^2/(Q t)^2)/2*Real.exp (-C t/2) := by
    have hq := hQpos t ht
    have hD := Real.exp_pos (-C t/2)
    have ha := pow_le_pow_left₀
      (mul_nonneg (sq_nonneg _) hq.le) (hangle t ht) 2
    have hE : (Real.exp (-C t/8))^4 = Real.exp (-C t/2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have ha' : δ^4*Real.exp (-C t/2)*(Q t)^2 ≤ (Y t)^4 := by
      simpa only [angleFloor,mul_pow,← pow_mul,show 2*2=4 by norm_num,hE] using ha
    have hb := mul_le_mul_of_nonneg_right (height t ⟨ht.1.le,ht.2.le⟩) (sq_nonneg (Y t))
    have hc : δ^4*(Q t)^2 ≤ Y₀^2*Real.exp (-C t/2)*(Y t)^2 := by
      apply (mul_le_mul_iff_of_pos_left hD).1
      nlinarith [ha',hb]
    apply (div_le_iff₀ (sq_pos_of_pos hY₀)).2
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hq)).1
    field_simp
    simp only [neg_div] at hc
    nlinarith [hc]
  have hK : 0 < 2*δ^4/Y₀^2 := by positivity
  have hm : AntitoneOn (fun t => Real.exp (-C t/2)+(2*δ^4/Y₀^2)*t) (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      ((Real.continuous_exp.comp_continuousOn (hC.neg.div_const 2)).add (continuousOn_id.const_mul _))
      (f' := fun t => Real.exp (-C t/2)*(-(4*(Y t)^2/(Q t)^2)/2)+2*δ^4/Y₀^2)
    · intro t ht
      rw [interior_Icc] at ht
      convert (((hdC t ht).neg.div_const 2).exp.add
          ((hasDerivAt_id t).const_mul (2*δ^4/Y₀^2))).hasDerivWithinAt
        (s := interior (Icc 0 T)) using 1 <;> first | rfl | (simp only [Pi.neg_apply]; ring)
    · intro t ht
      rw [interior_Icc] at ht
      nlinarith [rate t ht]
  have hb := hm ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT
  simp only [hCinit,neg_zero,zero_div,Real.exp_zero,mul_zero,add_zero] at hb
  have ht : T ≤ 1/(2*δ^4/Y₀^2) := (le_div_iff₀ hK).2 (by nlinarith [Real.exp_pos (-C T/2)])
  convert ht using 1; field_simp

lemma good_physical_clock {κ : ℝ} (hκ : 0 < κ ∧ κ < 8)
    {B : ℝ≥0 → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal) γ g f)
    (hc : Continuous B) {z : ℂ} (hz : z ∈ halfPlane) {δ v : ℝ}
    (hδ : 0 < δ) (hv : 0 < v)
    (hhit : firstLiveRadiusStop γ g z v ≠ (⊤ : ℝ≥0∞))
    (hgood : ∀ q : ℚ, 0 < (q:ℝ) → (q:ℝ) ≤ v →
      finiteStoppedDensity κ B γ g z q ∉ Ioo 0 (threshold κ z δ q)) :
    firstLiveRadiusStop γ g z v ≤ ENNReal.ofReal (z.im^2/(2*δ^4)) := by
  have hUc : Continuous (fun t : ℝ => Real.sqrt κ*B t.toNNReal) :=
    continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hU := hUc.continuousOn (s := Ici 0)
  obtain ⟨T,hstop,hzT,hrT⟩ := RadiusPast.live_radius_witness hm hU hhit
  have hT : 0 < (T:ℝ) := by
    have hp := hm.firstLiveRadiusStop_pos hU hz hv
    rw [hstop] at hp
    exact ENNReal.coe_pos.1 hp
  let C := fun t => Real.log (2*z.im)-Real.log (loewnerRadius g t z)
  have hC : ContinuousOn C (Icc 0 T) :=
    continuousOn_const.sub (hm.continuous_log_radius T.coe_nonneg (hU.mono Icc_subset_Ici_self) hzT)
  have hCs : StrictMonoOn C (Icc 0 T) := by
    intro a ha b hb hab
    have hh := hm.log_radius_strictAnti T.coe_nonneg (hU.mono Icc_subset_Ici_self) hzT ha hb hab
    dsimp [C]
    linarith
  have hC0 : C 0 = 0 := by simp only [C,hm.radius_initial hz,sub_self]
  have hCT : C T = v := by
    have hy : 0 < 2*z.im := by have : 0<z.im := hz; positivity
    dsimp [C]
    rw [hrT,Real.log_mul hy.ne' (Real.exp_ne_zero _),Real.log_exp]
    ring
  have hg := hm.continuous_eval T.coe_nonneg hzT
  have hsine : ContinuousOn (fun t => loewnerAngleSine κ B g t z) (Icc 0 T) := by
    have hh := (Complex.continuous_im.comp_continuousOn hg).div
      (hg.sub (Complex.continuous_ofReal.comp hUc).continuousOn).norm
      (fun t ht => norm_ne_zero_iff.2 (hm.centered_ne_zero ht.1 (survivingDomain_mono ht.2 hzT)))
    convert hh using 1; first | rfl | (funext t; simp only [loewnerAngleSine,Complex.ofReal_mul,Function.comp_def,Pi.div_apply,Pi.sub_apply])
  have hangle : ∀ t : ℝ, t ∈ Ioo 0 (T:ℝ) → angleFloor δ (C t) ≤ loewnerAngleSine κ B g t z := by
    have hF : ContinuousOn (fun t => loewnerAngleSine κ B g t z-angleFloor δ (C t)) (Icc 0 T) :=
      hsine.sub (continuousOn_const.mul (Real.continuous_exp.comp_continuousOn (hC.neg.div_const 8)))
    have hn := rational_clock_nonneg hT hC hCs hC0 hCT hF ?_
    · intro t ht
      exact sub_nonneg.1 (hn t ht)
    · intro q hq hqv s hs hseq
      apply sub_nonneg.2
      by_contra hn
      exact hgood q hq hqv (live_density_below hκ hm hc hs.1
        (survivingDomain_mono hs.2 hzT) hseq (by rw [← hseq]; exact lt_of_not_ge hn))
  have hbound : (T:ℝ) ≤ z.im^2/(2*δ^4) := by
    apply exponential_clock_bound (Y := fun t => (g t z).im) (C := C)
      (Q := fun t => Complex.normSq (g t z-((Real.sqrt κ*B t.toNNReal : ℝ) : ℂ)))
      T.coe_nonneg hδ (show 0<z.im from hz) (hm.initial z hz |>.symm ▸ rfl) hC0
      (Complex.continuous_im.comp_continuousOn hg) hC
    · intro t ht
      exact hm.im_pos ht.1 (survivingDomain_mono ht.2 hzT)
    · intro t ht
      exact Complex.normSq_pos.2 (hm.centered_ne_zero ht.1.le (survivingDomain_mono ht.2.le hzT))
    · intro t ht
      simp only [Complex.normSq_apply,Complex.sub_im,Complex.ofReal_im,sub_zero]
      nlinarith [sq_nonneg ((g t z-((Real.sqrt κ*B t.toNNReal : ℝ) : ℂ)).re)]
    · intro t ht
      have hp := norm_pos_iff.2 (hm.centered_ne_zero ht.1.le (survivingDomain_mono ht.2.le hzT))
      have hs := hangle t ht
      simp only [loewnerAngleSine,← Complex.ofReal_mul] at hs
      have ha := (le_div_iff₀ hp).1 hs
      have hb := pow_le_pow_left₀ (mul_nonneg (angleFloor_pos hδ _).le hp.le) ha 2
      simpa only [mul_pow,Complex.normSq_eq_norm_sq] using hb
    · intro t ht
      exact hm.hasDerivAt_height ht.1 (survivingDomain_mono ht.2.le hzT)
    · intro t ht
      apply ((hm.hasDerivAt_log_radius T.coe_nonneg (hU.mono Icc_subset_Ici_self) hzT ht).const_sub
        (Real.log (2*z.im))).congr_deriv
      ring
  rw [hstop]
  simpa only [ENNReal.ofReal_coe_nnreal] using (ENNReal.ofReal_le_ofReal hbound)

end SLEExactGauge.FiniteClock

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open FiniteClock

theorem finiteCenteredPhysicalTime_tight {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ u : ℝ, 1 ≤ u →
      (finiteCenteredMeasure κ P B γ g z u)
        {sample | ENNReal.ofReal T < firstLiveRadiusStop (γ sample) (g sample) z u}
        < ENNReal.ofReal ε := by
  obtain ⟨D,hD,hbound⟩ := bad_bound κ hκ B hB γ g f hγ hmaps z hz
  obtain ⟨δ,hδ,hsmall⟩ := exists_small_floor (exponent_pos hκ) hD hε
  refine ⟨z.im^2/(2*δ^4),by have hy : 0<z.im := hz; positivity,?_⟩
  intro u hu
  have hu0 : 0 < u := by linarith
  let Q := finiteCenteredMeasure κ P B γ g z u
  have hQP : Q ≪ P := withDensity_absolutelyContinuous _ _
  have hhit : ∀ᵐ sample ∂Q, firstLiveRadiusStop (γ sample) (g sample) z u ≠ (⊤ : ℝ≥0∞) := by
    change ∀ᵐ sample ∂P.withDensity _,_
    rw [ae_withDensity_iff' ((finiteStoppedDensity_aemeasurable κ hκ B hB γ g f hmaps z hz u hu0).div_const _)]
    exact Filter.Eventually.of_forall (fun sample hn ht => hn (by simp only [finiteStoppedDensity,ht,ite_true,ENNReal.zero_div]))
  have hsub : {sample | ENNReal.ofReal (z.im^2/(2*δ^4)) <
        firstLiveRadiusStop (γ sample) (g sample) z u} ≤ᵐ[Q] bad κ B γ g z δ u := by
    filter_upwards [hQP.ae_le hmaps,hQP.ae_le hB.cont,hhit] with sample hm hc hh hx
    by_contra hn
    have hg : ∀ q : ℚ, 0 < (q:ℝ) → (q:ℝ) ≤ u →
        finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z q ∉ Ioo 0 (threshold κ z δ q) := by
      intro q hq hqu hbad
      exact hn (mem_bad_of_rational κ B γ g z δ u q hq hqu hbad)
    exact not_lt_of_ge (good_physical_clock (κ := κ) (B := fun t => B t sample) (γ := γ sample)
      (g := g sample) (f := f sample) hκ hm hc hz hδ hu0 hh hg) hx
  exact (measure_mono_ae hsub).trans_lt
    ((hbound δ hδ u).trans_lt (ENNReal.ofReal_lt_ofReal_iff hε |>.2 hsmall))

end SLEExactGauge

end

end

end OAI
