import Mathlib
import OAI.Probability.SLE.InteriorEntrance

namespace OAI

/-! Interior Disk Proof for chordal SLE. -/

section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma access_positive_height_cut {η : ℝ → ℂ} {T ε : ℝ}
    (hT : 0 < T) (hc : ContinuousOn η (Icc 0 T)) (h0 : η 0 = 0)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < (η t).im) (hε : 0 < ε) :
    ∃ s ∈ Ioo 0 T, ‖η s‖ < ε ∧ ∀ t ∈ Icc s T, (η s).im ≤ (η t).im := by
  have hc0 := Metric.continuousWithinAt_iff.mp (hc 0 ⟨le_rfl,hT.le⟩)
  obtain ⟨δ,hδ,hδlim⟩ := hc0 ε hε
  let a : ℝ := min (T/2) (δ/2)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have haT : a < T := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨m,hm,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc a T).Nonempty from ⟨a,le_rfl,haT.le⟩)
    ((Complex.continuous_im.comp_continuousOn hc).mono (Icc_subset_Icc_left ha.le))
  have hmpos : 0 < (η m).im := hpos m ⟨ha.trans_le hm.1,hm.2⟩
  obtain ⟨δ',hδ',hδlim'⟩ := hc0 (η m).im hmpos
  let b : ℝ := min (a/2) (δ'/2)
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  have hba : b < a := (min_le_left _ _).trans_lt (by linarith)
  have hbT : b < T := hba.trans haT
  have hbnorm : ‖η b‖ < (η m).im := by
    have hh := hδlim' ⟨hb.le,hbT.le⟩
      (show dist b 0 < δ' by
        rw [Real.dist_eq,sub_zero,abs_of_pos hb]
        exact (min_le_right _ _).trans_lt (by linarith))
    simpa only [h0,dist_zero_right] using hh
  obtain ⟨s,hs,hsmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc b T).Nonempty from ⟨b,le_rfl,hbT.le⟩)
    ((Complex.continuous_im.comp_continuousOn hc).mono (Icc_subset_Icc_left hb.le))
  have hsa : s < a := by
    by_contra hh
    have hh₁ := hmin ⟨not_lt.mp hh,hs.2⟩
    have hh₂ := hsmin ⟨le_rfl,hbT.le⟩
    have hh₃ := Complex.im_le_norm (η b)
    change (η m).im ≤ (η s).im at hh₁
    change (η s).im ≤ (η b).im at hh₂
    linarith
  refine ⟨s,⟨hb.trans_le hs.1,hsa.trans haT⟩,?_,?_⟩
  · have hh := hδlim ⟨(hb.trans_le hs.1).le,hs.2⟩
      (show dist s 0 < δ by
        rw [Real.dist_eq,sub_zero,abs_of_pos (hb.trans_le hs.1)]
        exact hsa.trans_le ((min_le_right _ _).trans (by linarith)))
    simpa only [h0,dist_zero_right] using hh
  · intro t ht
    exact hsmin ⟨hs.1.trans ht.1,ht.2⟩

lemma measure_eventually_mem_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (E : ℕ → Set Ω) (b : ℝ≥0∞) (hb : ∀ n, P (E n) ≤ b) :
    P {xi | ∀ᶠ n in atTop, xi ∈ E n} ≤ b := by
  let A : ℕ → Set Ω := fun m => {xi | ∀ n, m ≤ n → xi ∈ E n}
  have hm : Monotone A := by
    intro i j hij xi hxi n hjn
    exact hxi n (hij.trans hjn)
  have he : {xi | ∀ᶠ n in atTop, xi ∈ E n} = ⋃ m, A m := by
    ext xi
    simp only [mem_ofPred_eq, mem_iUnion, Filter.eventually_atTop, A]
  rw [he,hm.measure_iUnion]
  apply iSup_le
  intro n
  exact (measure_mono (show A n ⊆ E n from fun xi hxi => hxi n le_rfl)).trans (hb n)
end SLEExactGauge
namespace SLEExactGauge

lemma positive_affine_im {a z : ℂ} {c : ℝ} (ha : 0 < a.im)
    (hc : 0 < c) (hz : 0 ≤ z.im) : 0 < (a+(c:ℂ)*z).im := by
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  positivity

lemma positive_affine_chart {F : ℂ → ℂ} {a : ℂ} {c : ℝ}
    (hF : DifferentiableOn ℂ F {z | 0 < z.im}) (hi : InjOn F {z | 0 < z.im})
    (ha : 0 < a.im) (hc : 0 < c) :
    DifferentiableOn ℂ (fun z => F (a+(c:ℂ)*z)) {z | 0 < z.im} ∧
    InjOn (fun z => F (a+(c:ℂ)*z)) {z | 0 < z.im} ∧
    ContinuousOn (fun z => (F (a+(c:ℂ)*z) : OnePoint ℂ)) {z : ℂ | 0 ≤ z.im} := by
  have haff : Differentiable ℂ (fun z : ℂ => a+(c:ℂ)*z) := by fun_prop
  have hm (z : ℂ) (hz : 0 ≤ z.im) := positive_affine_im ha hc hz
  refine ⟨hF.comp haff.differentiableOn (fun z hz => hm z hz.le),?_,?_⟩
  · intro z hz w hw heq
    have hh := add_left_cancel (hi (hm z hz.le) (hm w hw.le) heq)
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne') hh
  · apply OnePoint.continuous_coe.comp_continuousOn
    exact hF.continuousOn.comp haff.continuous.continuousOn (fun z hz => hm z hz)

lemma affine_access_cut {F : ℂ → ℂ} {η : ℝ → ℂ} {T s r : ℝ} {q : ℂ}
    (_hT : 0 < T) (hc : ContinuousOn η (Icc 0 T))
    (hs : s ∈ Ioo 0 T) (_hpos : ∀ t ∈ Ioc 0 T, 0 < (η t).im)
    (hpath : ∀ t ∈ Ioc 0 T, ‖F (η t)-q‖ ≤ r)
    (hmin : ∀ t ∈ Icc s T, (η s).im ≤ (η t).im)
    (hsmall : (η s).im < (η T).im) (hq : F (η T) = q) :
    let c := ‖η T-η s‖
    let ξ := fun t : ℝ => (η (s+t)-η s)/(c:ℂ)
    0 < c ∧ ContinuousOn ξ (Icc 0 (T-s)) ∧ ξ 0 = 0 ∧
    ‖ξ (T-s)‖ = 1 ∧ 0 < (ξ (T-s)).im ∧
    F (η s+(c:ℂ)*ξ (T-s)) = q ∧
    (∀ t ∈ Icc 0 (T-s), 0 ≤ (ξ t).im) ∧
    (∀ t ∈ Icc 0 (T-s), ∃ w : ℂ,
      (F (η s+(c:ℂ)*ξ t) : OnePoint ℂ) = (w : OnePoint ℂ) ∧ ‖w-q‖ ≤ r) := by
  dsimp only
  let c : ℝ := ‖η T-η s‖
  have hne : η T-η s ≠ 0 := by
    intro he
    have hh := congrArg Complex.im (sub_eq_zero.mp he)
    linarith
  have hcp : 0 < c := norm_pos_iff.mpr hne
  have hcz : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcp.ne'
  have hm {t : ℝ} (ht : t ∈ Icc 0 (T-s)) : s+t ∈ Ioc 0 T := by
    constructor <;> linarith [ht.1,ht.2,hs.1]
  have hcancel (t : ℝ) : η s+(c:ℂ)*((η (s+t)-η s)/(c:ℂ)) = η (s+t) := by
    field_simp
    ring
  have hend : s+(T-s) = T := by ring
  change 0 < c ∧ _
  refine ⟨hcp,?_,?_,?_,?_,?_,?_,?_⟩
  · apply (hc.comp (continuous_const.add continuous_id).continuousOn
      (fun t ht => ⟨(hm ht).1.le,(hm ht).2⟩)).sub continuousOn_const |>.div_const (c:ℂ)
  · simp
  · simp only [hend,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_norm]
    exact div_self hcp.ne'
  · simp only [hend,Complex.div_ofReal_im,Complex.sub_im]
    exact div_pos (sub_pos.mpr hsmall) hcp
  · rw [hcancel,hend,hq]
  · intro t ht
    simp only [Complex.div_ofReal_im,Complex.sub_im]
    exact div_nonneg (sub_nonneg.mpr (hmin (s+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩)) hcp.le
  · intro t ht
    refine ⟨F (η (s+t)),?_,hpath _ (hm ht)⟩
    rw [hcancel]

end SLEExactGauge
namespace SLEExactGauge
 

def SourceInteriorDiskRuleTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ γ : Ω → ℝ≥0 → ℂ, IsOrdinaryChordalSLE κ γ P →
    ∀ F : ℂ → ℂ,
    DifferentiableOn ℂ F {z | 0 < z.im} → InjOn F {z | 0 < z.im} →
    ∀ (q : ℂ) (r : ℝ), 0 < r →
    ∀ (η : ℝ → ℂ) (T : ℝ), 0 < T → ContinuousOn η (Icc 0 T) →
    η 0 = 0 → ‖η T‖ = 1 → F (η T) = q →
    (∀ t ∈ Ioc 0 T, 0 < (η t).im) →
    (∀ t ∈ Ioc 0 T, ‖F (η t)-q‖ ≤ r) →
    ∀ L : ℝ, 1 ≤ L →
      P {xi | ∃ t : ℝ≥0, η T ∈ survivingDomain (γ xi) t ∧
        0 < (γ xi t).im ∧ L*r < ‖F (γ xi t)-q‖} ≤
        ENNReal.ofReal (C*L^(-c))

theorem sourceInteriorDiskRule_proved : SourceInteriorDiskRuleTarget := by
  intro κ hκ hκ8
  obtain ⟨C,c,hC,hc,hbound⟩ := sourceChartedDiskRule κ hκ hκ8
  refine ⟨C,c,hC,hc,?_⟩
  intro Ω mΩ P hP γ hγ F hF hi q r hr η T hT hη h0 hu hq hpos hpath L hL
  let : IsProbabilityMeasure P := hP
  have huim : 0 < (η T).im := hpos T ⟨hT,le_rfl⟩
  have hsmall (n : ℕ) : 0 < min (1/((n:ℝ)+1)) ((η T).im/2) := by positivity
  choose s hs hnorm hmin using fun n : ℕ => access_positive_height_cut hT hη h0 hpos (hsmall n)
  let a : ℕ → ℂ := fun n => η (s n)
  let d : ℕ → ℝ := fun n => ‖η T-a n‖
  let u : ℕ → ℂ := fun n => (η T-a n)/(d n:ℂ)
  let Ψ : ℕ → ℂ → ℂ := fun n z => F (a n+(d n:ℂ)*z)
  let ξ : ℕ → ℝ → ℂ := fun n t => (η (s n+t)-a n)/(d n:ℂ)
  have hn (n : ℕ) : ‖a n‖ < 1/((n:ℝ)+1) := (hnorm n).trans_le (min_le_left _ _)
  have hasmall (n : ℕ) : (a n).im < (η T).im := by
    have hh := (hnorm n).trans_le (min_le_right _ _)
    have hh' := Complex.im_le_norm (a n)
    change ‖a n‖ < _ at hh
    linarith
  have hcut (n : ℕ) := affine_access_cut hT hη (hs n) hpos hpath (hmin n) (hasmall n) hq
  have hdp (n : ℕ) : 0 < d n := (hcut n).1
  have hai (n : ℕ) : 0 < (a n).im := hpos (s n) ⟨(hs n).1,(hs n).2.le⟩
  have ha0 : Tendsto a atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ε hε
    refine ⟨N,fun n hnn => ?_⟩
    rw [dist_zero_right]
    exact (hn n).trans (by simpa only [Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0 < 1/((n:ℝ)+1))] using hN n hnn)
  have hd1 : Tendsto d atTop (𝓝 1) := by
    have hh := ((tendsto_const_nhds (x := η T)).sub ha0).norm
    simpa only [sub_zero,hu] using hh
  have hu1 : Tendsto u atTop (𝓝 (η T)) := by
    have hh := ((tendsto_const_nhds (x := η T)).sub ha0).div (Complex.continuous_ofReal.tendsto 1 |>.comp hd1)
      (by norm_num : (1:ℂ) ≠ 0)
    convert hh using 1
    · ext n
      simp only [u,Pi.div_apply,Function.comp_apply]
    · simp
  let E : ℕ → Set Ω := fun n => {xi | ∃ t : ℝ≥0, u n ∈ survivingDomain (γ xi) t ∧
    (Ψ n (γ xi t) : OnePoint ℂ) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (L*r)}
  have hE (n : ℕ) : P (E n) ≤ ENNReal.ofReal (C*L^(-c)) := by
    have hh := hcut n
    obtain ⟨hd,hct,hz,hnormT,hposT,hqT,hupper,hpaths⟩ := hh
    have hξ : ξ n (T-s n) = u n := by simp only [ξ,u, show s n+(T-s n)=T by ring]
    obtain ⟨hFn,hin,hbc⟩ := positive_affine_chart hF hi (hai n) (hdp n)
    have hb := hbound Ω mΩ P hP γ hγ (Ψ n) (fun z => (Ψ n z : OnePoint ℂ))
      hFn hin hbc (fun _ _ => rfl) q r hr (ξ n) (T-s n) (sub_pos.mpr (hs n).2)
      hct hz hnormT hposT hqT hupper hpaths L hL
    simpa only [hξ] using hb
  have hf (z : ℂ) (hz : 0 < z.im) : Tendsto (fun n => Ψ n z) atTop (𝓝 (F z)) := by
    have harg : Tendsto (fun n => a n+(d n:ℂ)*z) atTop (𝓝 z) := by
      have hh := ha0.add ((Complex.continuous_ofReal.tendsto 1 |>.comp hd1).mul (tendsto_const_nhds (x := z)))
      convert hh using 1
      · ext n
        simp only [Function.comp_apply]
      · simp
    exact (hF.continuousOn.continuousAt (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hz)).tendsto.comp harg
  obtain ⟨B,G,Fw,hB,hw⟩ := hγ.exists_charts
  have hsub : {xi | ∃ t : ℝ≥0, η T ∈ survivingDomain (γ xi) t ∧
      0 < (γ xi t).im ∧ L*r < ‖F (γ xi t)-q‖} ≤ᵐ[P]
      {xi | ∀ᶠ n in atTop, xi ∈ E n} := by
    filter_upwards [hw] with xi hxi
    rintro ⟨t,ht,hzi,hbig⟩
    have hlive := hu1.eventually ((isOpen_survivingDomain hxi.1 t).eventually_mem ht)
    have hnormlim := ((hf (γ xi t) hzi).sub_const q).norm
    have hbig' := hnormlim.eventually (eventually_gt_nhds hbig)
    filter_upwards [hlive,hbig'] with n hnt hnb
    refine ⟨t,hnt,?_⟩
    rintro ⟨w,hwball,hweq⟩
    have heq : w = Ψ n (γ xi t) := OnePoint.coe_injective hweq
    subst w
    exact (not_lt_of_ge hnb.le) (by simpa only [Metric.mem_ball,dist_eq_norm] using hwball)
  exact (measure_mono_ae hsub).trans (measure_eventually_mem_le P E _ hE)

end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

def sourceScaleTime (c t : ℝ≥0) : ℝ≥0 := t / c ^ 2

def sourceScaleTrace (c : ℝ≥0) (γ : ℝ≥0 → ℂ) (t : ℝ≥0) : ℂ :=
  (c : ℂ) * γ (sourceScaleTime c t)

def sourceScaleChart (c : ℝ≥0) (F : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) : ℂ :=
  (c : ℂ) * F (sourceScaleTime c t) (z / (c : ℂ))

universe u_source_scale
 

def SourceCapacityScalingTarget : Prop :=
  (∀ (c : ℝ≥0), 0 < c → ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F →
    IsCapacityTwoWitness (fun t => (c : ℝ) * U (sourceScaleTime c t))
      (sourceScaleTrace c γ) (sourceScaleChart c G) (sourceScaleChart c F)) ∧
  (∀ {Ω : Type u_source_scale} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ), 0 < κ → κ < 8 → ∀ (γ : Ω → ℝ≥0 → ℂ),
    IsOrdinaryChordalSLE κ γ P → ∀ (c : ℝ≥0), 0 < c →
    IsOrdinaryChordalSLE κ (fun ω => sourceScaleTrace c (γ ω)) P)
end
end SLEExactGauge
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_scale_time_image (c t : ℝ≥0) (hc : 0 < c) :
    sourceScaleTime c '' Icc 0 t = Icc 0 (sourceScaleTime c t) := by
  ext s
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨bot_le, div_le_div_of_nonneg_right hu.2 (by positivity)⟩
  · intro hs
    refine ⟨s * c ^ 2, ⟨bot_le, ?_⟩, ?_⟩
    · exact (le_div_iff₀ (pow_pos hc 2)).mp hs.2
    · simp [sourceScaleTime, ne_of_gt hc]

lemma source_scale_past (c t : ℝ≥0) (hc : 0 < c) (γ : ℝ≥0 → ℂ) :
    sourceScaleTrace c γ '' Icc 0 t =
      (fun z : ℂ => (c : ℂ) * z) '' (γ '' Icc 0 (sourceScaleTime c t)) := by
  rw [← source_scale_time_image c t hc, ← image_comp, ← image_comp]
  rfl

lemma source_scale_halfplane (c : ℝ≥0) (hc : 0 < c) :
    (fun z : ℂ => (c : ℂ) * z) '' upperHalfPlane = upperHalfPlane := by
  have hcR : 0 < (c : ℝ) := hc
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [upperHalfPlane, mem_ofPred_eq, mul_im, ofReal_re, ofReal_im, zero_mul,
      add_zero] at *
    exact mul_pos hcR hx
  · intro hz
    refine ⟨z / (c : ℂ), ?_, mul_div_cancel₀ z hcC⟩
    simpa only [upperHalfPlane, mem_ofPred_eq, div_ofReal_im] using
      div_pos hz hcR

lemma source_scale_bounded (c : ℂ) (hc : c ≠ 0) (s : Set ℂ) :
    Bornology.IsBounded ((fun z => c * z) '' s) ↔ Bornology.IsBounded s := by
  constructor
  · intro hs
    have hh := (hs.isCompact_closure.image
      (show Continuous (fun z : ℂ => z / c) by fun_prop)).isBounded
    have he : (fun z : ℂ => z / c) '' ((fun z => c*z) '' s) = s := by
      simp only [image_image]
      simp [mul_div_cancel_left₀ _ hc]
    rw [← he]
    exact hh.subset (image_mono subset_closure)
  · intro hs
    exact (hs.isCompact_closure.image (show Continuous (fun z : ℂ => c*z) by
      fun_prop)).isBounded.subset (image_mono subset_closure)

lemma source_scale_domain (c t : ℝ≥0) (hc : 0 < c) (γ : ℝ≥0 → ℂ) :
    survivingDomain (sourceScaleTrace c γ) t =
      (fun z : ℂ => (c : ℂ)*z) '' survivingDomain γ (sourceScaleTime c t) := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  let e := Homeomorph.mulLeft₀ (c : ℂ) hcC
  have he : (e : ℂ → ℂ) = fun z => (c : ℂ)*z := rfl
  have HD : upperHalfPlane \ (sourceScaleTrace c γ '' Icc 0 t) =
      e '' (upperHalfPlane \ γ '' Icc 0 (sourceScaleTime c t)) := by
    rw [image_sdiff e.injective, he, source_scale_halfplane c hc, source_scale_past c t hc γ]
  ext z
  constructor
  · rintro ⟨hz, hbound⟩
    rw [HD] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro hb
    apply hbound
    rw [HD, ← e.image_connectedComponentIn hx, he]
    exact (source_scale_bounded _ hcC _).2 hb
  · rintro ⟨x, ⟨hx, hb⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [HD]
      exact mem_image_of_mem e hx
    · intro hbound
      apply hb
      change Bornology.IsBounded (connectedComponentIn
        (upperHalfPlane \ sourceScaleTrace c γ '' Icc 0 t) (e x)) at hbound
      rw [HD, ← e.image_connectedComponentIn hx, he] at hbound
      exact (source_scale_bounded _ hcC _).1 hbound

lemma source_scale_domain_iff (c t : ℝ≥0) (hc : 0 < c) (γ : ℝ≥0 → ℂ) (z : ℂ) :
    z ∈ survivingDomain (sourceScaleTrace c γ) t ↔
      z / (c : ℂ) ∈ survivingDomain γ (sourceScaleTime c t) := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [source_scale_domain c t hc γ]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_div_cancel_left₀ _ hcC] using hx
  · intro hz
    exact ⟨z/(c : ℂ), hz, mul_div_cancel₀ z hcC⟩
end
end SLEExactGauge
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_scale_halfplane_iff (c : ℝ≥0) (hc : 0 < c) (z : ℂ) :
    z / (c : ℂ) ∈ upperHalfPlane ↔ z ∈ upperHalfPlane := by
  change 0 < (z / (c : ℂ)).im ↔ 0 < z.im
  rw [div_ofReal_im, div_pos_iff_of_pos_right (show 0 < (c : ℝ) from hc)]

lemma source_scale_witness (c : ℝ≥0) (hc : 0 < c) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ) (hw : IsCapacityTwoWitness U γ G F) :
    IsCapacityTwoWitness (fun t => (c : ℝ) * U (sourceScaleTime c t))
      (sourceScaleTrace c γ) (sourceScaleChart c G) (sourceScaleChart c F) := by
  have hcR : 0 < (c : ℝ) := hc
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hcm (z : ℂ) : (c : ℂ)*z ∈ upperHalfPlane ↔ z ∈ upperHalfPlane := by
    change 0 < ((c : ℂ)*z).im ↔ 0 < z.im
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    exact mul_pos_iff_of_pos_left hcR
  rcases hw with ⟨hγ, hγ0, hIm, hG, hF, hGmap, hFmap, hFG, hGF, hG0, hD, hInf, hLim⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have ht : Continuous (sourceScaleTime c) := by unfold sourceScaleTime; fun_prop
    exact continuous_const.mul (hγ.comp ht)
  · simp [sourceScaleTrace, sourceScaleTime, hγ0]
  · intro t
    simpa only [sourceScaleTrace, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
      using mul_nonneg hcR.le (hIm (sourceScaleTime c t))
  · intro t
    exact (differentiableOn_const (c : ℂ)).mul ((hG (sourceScaleTime c t)).comp
      (differentiableOn_id.div_const _) (fun z hz => (source_scale_domain_iff c t hc γ z).1 hz))
  · intro t
    exact (differentiableOn_const (c : ℂ)).mul ((hF (sourceScaleTime c t)).comp
      (differentiableOn_id.div_const _) (fun z hz => (source_scale_halfplane_iff c hc z).2 hz))
  · intro t z hz
    exact (hcm _).2 (hGmap _ ((source_scale_domain_iff c t hc γ z).1 hz))
  · intro t z hz
    apply (source_scale_domain_iff c t hc γ _).2
    simpa [sourceScaleChart, hcC] using hFmap (sourceScaleTime c t)
      ((source_scale_halfplane_iff c hc z).2 hz)
  · intro t z hz
    dsimp [sourceScaleChart]
    rw [mul_div_cancel_left₀ _ hcC, hFG _ _ ((source_scale_domain_iff c t hc γ z).1 hz)]
    exact mul_div_cancel₀ z hcC
  · intro t z hz
    dsimp [sourceScaleChart]
    rw [mul_div_cancel_left₀ _ hcC, hGF _ _ ((source_scale_halfplane_iff c hc z).2 hz)]
    exact mul_div_cancel₀ z hcC
  · intro z hz
    simp only [sourceScaleChart, sourceScaleTime, zero_div]
    rw [hG0 _ ((source_scale_halfplane_iff c hc z).2 hz)]
    exact mul_div_cancel₀ z hcC
  · intro t z hz
    have hd := hD (sourceScaleTime c t) (z / (c : ℂ))
      ((source_scale_domain_iff c t hc γ z).1 hz)
    simp only [sourceScaleTime, NNReal.coe_div, NNReal.coe_pow] at hd
    have htime : HasDerivWithinAt (fun u : ℝ => u / (c : ℝ)^2) (1/(c : ℝ)^2)
        (Ici 0) (t : ℝ) := ((hasDerivAt_id (t : ℝ)).div_const _).hasDerivWithinAt
    have hs := (hd.scomp (t : ℝ) htime (fun u hu => div_nonneg hu (sq_nonneg _))).const_smul
      (c : ℂ)
    have he (u : ℝ) : Real.toNNReal (u / (c : ℝ)^2) = sourceScaleTime c (Real.toNNReal u) := by
      simp only [Real.toNNReal_div' (sq_nonneg _), Real.toNNReal_pow (by positivity),
        Real.toNNReal_coe, sourceScaleTime]
    change HasDerivWithinAt
      (fun u : ℝ => (c : ℂ) * G (Real.toNNReal (u / (c : ℝ)^2)) (z/(c : ℂ)))
      ((c : ℂ) * ((1/(c : ℝ)^2) • (2 / (G (t / c^2) (z/(c : ℂ)) - (U (t/c^2) : ℂ)))))
      (Ici 0) (t : ℝ) at hs
    simp only [he] at hs
    convert hs using 1 <;>
      simp only [sourceScaleChart, sourceScaleTime, Complex.real_smul, ofReal_mul,
        ofReal_div, ofReal_one, ofReal_pow]
    field_simp [hcC]
  · intro t
    let e := Homeomorph.mulLeft₀ ((c : ℂ)⁻¹) (inv_ne_zero hcC)
    have hco : Tendsto (fun z : ℂ => z/(c : ℂ)) (cocompact ℂ) (cocompact ℂ) := by
      have hh : Tendsto e (cocompact ℂ) (cocompact ℂ) := le_of_eq e.map_cocompact
      change Tendsto (fun z : ℂ => (c : ℂ)⁻¹ * z) (cocompact ℂ) (cocompact ℂ) at hh
      simpa only [div_eq_mul_inv, mul_comm] using hh
    have hp : Tendsto (fun z : ℂ => z/(c : ℂ))
        (𝓟 (survivingDomain (sourceScaleTrace c γ) t))
        (𝓟 (survivingDomain γ (sourceScaleTime c t))) :=
      tendsto_principal_principal.mpr (fun z hz => (source_scale_domain_iff c t hc γ z).1 hz)
    have hh := ((hInf (sourceScaleTime c t)).comp (hco.inf hp)).const_mul ((c : ℂ)^2)
    convert hh using 1
    · ext z
      dsimp [Function.comp_def, sourceScaleChart]
      field_simp
    · simp only [sourceScaleTime, NNReal.coe_div, NNReal.coe_pow, ofReal_div, ofReal_pow]
      field_simp
  · intro t
    have hy : Tendsto (fun y : ℝ => y/(c : ℝ)) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa using ((continuous_id.div_const (c : ℝ)).continuousAt.tendsto.mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds))
      · exact eventually_nhdsWithin_of_forall (fun y hy => div_pos hy hcR)
    have hh := ((hLim (sourceScaleTime c t)).comp hy).const_mul (c : ℂ)
    convert hh using 1
    · ext y
      dsimp [Function.comp_def, sourceScaleChart]
      congr 1
      push_cast
      field_simp
    · rfl
end
end SLEExactGauge
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

theorem sourceCapacityScaling : SourceCapacityScalingTarget := by
  refine ⟨source_scale_witness, ?_⟩
  intro Ω m P κ hκ hκ8 γ hγ c hc
  rcases hγ with ⟨hm, B, hB, hw⟩
  refine ⟨fun t => measurable_const.mul (hm (sourceScaleTime c t)),
    (fun t ω => (c : ℝ) * B (sourceScaleTime c t) ω), ?_, ?_⟩
  · have hh := hB.smul (c := (c ^ 2)⁻¹) (inv_ne_zero (pow_ne_zero 2 hc.ne'))
    simpa only [sourceScaleTime, NNReal.coe_inv, NNReal.coe_pow, Real.sqrt_inv,
      Real.sqrt_sq c.coe_nonneg, inv_inv, div_eq_mul_inv, mul_comm] using hh
  · filter_upwards [hw] with ω hω
    obtain ⟨G, F, hGF⟩ := hω
    refine ⟨sourceScaleChart c G, sourceScaleChart c F, ?_⟩
    have hh := source_scale_witness c hc (fun t => Real.sqrt κ * B t ω) (γ ω) G F hGF
    simpa only [mul_left_comm (c : ℝ) (Real.sqrt κ)] using hh
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma source_interior_disk_unnormalized (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8) :
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ γ : Ω → ℝ≥0 → ℂ, IsOrdinaryChordalSLE κ γ P →
    ∀ F : ℂ → ℂ,
    DifferentiableOn ℂ F upperHalfPlane → InjOn F upperHalfPlane →
    ∀ (q : ℂ) (r : ℝ), 0 < r →
    ∀ (η : ℝ → ℂ) (T : ℝ), 0 < T → ContinuousOn η (Icc 0 T) →
    η 0 = 0 → F (η T) = q →
    (∀ t ∈ Ioc 0 T, 0 < (η t).im) →
    (∀ t ∈ Ioc 0 T, ‖F (η t)-q‖ ≤ r) →
    ∀ L : ℝ, 1 ≤ L →
      P {xi | ∃ t : ℝ≥0, η T ∈ survivingDomain (γ xi) t ∧
        0 < (γ xi t).im ∧ L*r < ‖F (γ xi t)-q‖} ≤
        ENNReal.ofReal (C*L^(-c)) := by
  obtain ⟨C,c,hC,hc,hbound⟩ := sourceInteriorDiskRule_proved κ hκ hκ8
  refine ⟨C,c,hC,hc,?_⟩
  intro Ω mΩ P hP γ hγ F hF hi q r hr η T hT hη hη0 hq hupper hpath L hL
  let d : ℝ≥0 := ‖η T‖₊
  have hd : 0 < d := by
    exact nnnorm_pos.mpr (fun he => by simpa [he] using hupper T ⟨hT,le_rfl⟩)
  let a : ℝ≥0 := d⁻¹
  have ha : 0 < a := inv_pos.mpr hd
  have hane : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let Ψ : ℂ → ℂ := fun z => F (z/(a : ℂ))
  let ξ : ℝ → ℂ := fun t => (a : ℂ)*η t
  have hmap (z : ℂ) (hz : z ∈ upperHalfPlane) : z/(a : ℂ) ∈ upperHalfPlane := by
    exact (source_scale_halfplane_iff a ha z).mpr hz
  have hΨ : DifferentiableOn ℂ Ψ upperHalfPlane :=
    hF.comp (differentiable_id.div_const (a : ℂ)).differentiableOn hmap
  have hΨi : InjOn Ψ upperHalfPlane := by
    intro x hx y hy he
    exact (div_left_inj' hane).mp (hi (hmap x hx) (hmap y hy) he)
  have hξ : ContinuousOn ξ (Icc 0 T) := continuousOn_const.mul hη
  have hξnorm : ‖ξ T‖ = 1 := by
    simp only [ξ,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg a.coe_nonneg]
    change (d : ℝ)⁻¹ * (d : ℝ) = 1
    exact inv_mul_cancel₀ (by exact_mod_cast hd.ne')
  have hΨξ (t : ℝ) : Ψ (ξ t) = F (η t) := by
    simp only [Ψ,ξ,mul_div_cancel_left₀ _ hane]
  have hξup (t : ℝ) (ht : t ∈ Ioc 0 T) : 0 < (ξ t).im := by
    simpa only [ξ, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_pos (show 0 < (a : ℝ) from ha) (hupper t ht)
  have hγa := sourceCapacityScaling.2 κ (by linarith) hκ8 γ hγ a ha
  have hb := hbound Ω mΩ P hP (fun ω => sourceScaleTrace a (γ ω)) hγa Ψ hΨ hΨi q r hr
    ξ T hT hξ (by simp [ξ,hη0]) hξnorm (by simpa [hΨξ] using hq) hξup
    (fun t ht => by simpa only [hΨξ] using hpath t ht) L hL
  apply (measure_mono ?_).trans hb
  rintro ω ⟨t,hl,ht,hb⟩
  let s : ℝ≥0 := t*a^2
  have hs : sourceScaleTime a s = t := by dsimp [s,sourceScaleTime]; exact mul_div_cancel_right₀ _ (pow_ne_zero 2 ha.ne')
  have htip : sourceScaleTrace a (γ ω) s = (a : ℂ)*γ ω t := by simp only [sourceScaleTrace,hs]
  refine ⟨s,?_,?_,?_⟩
  · apply (source_scale_domain_iff a s ha (γ ω) (ξ T)).mpr
    simpa only [ξ, mul_div_cancel_left₀ _ hane, hs] using hl
  · rw [htip]
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_pos (show 0 < (a : ℝ) from ha) ht
  · simpa only [htip,Ψ,mul_div_cancel_left₀ _ hane] using hb
end SLEExactGauge
end

end OAI
