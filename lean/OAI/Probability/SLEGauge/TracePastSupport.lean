import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.PastHullSupport

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.TraceLevelLocalization
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen ExactSLEFiniteTilt

 

lemma compact_away_angle_large (κ : ℝ) (hκ : 0<κ) (b : TDriver)
    (hb : AngularRegular κ b) (hcont : ContinuousOn (Target.trace κ b) (Ici 0))
    (T : ℝ≥0) (K : Set UpperPlane) (hK : IsCompact K)
    (haway : ∀ z∈K, z.1∉(Target.trace κ b) '' Icc 0 ((T:ℝ)/κ))
    (C : ℝ) (hC : 0≤C) :
    ∀ᶠ j : ℕ in atTop, ∀ z∈K,
      let τ := radialTime (Target.a κ) (driverHomeomorph b).1 z.1
        (z.1.im*Real.exp (-2*(Target.a κ)*(j+1)))
      τ≤(T:ℝ≥0∞) →
      let v := actualState (Target.a κ) (driverHomeomorph b).1 τ.toNNReal z.1
      C < |X v/Y v| := by
  by_cases hne : K.Nonempty
  · have hc : ContinuousOn (fun z : UpperPlane => z.1.im) K :=
      (Complex.continuous_im.comp continuous_subtype_val).continuousOn
    obtain ⟨zlo,hzlo,hmin⟩ := hK.exists_isMinOn hne hc
    obtain ⟨zhi,hzhi,hmax⟩ := hK.exists_isMaxOn hne hc
    have htr : IsCompact ((Target.trace κ b) '' Icc 0 ((T:ℝ)/κ)) :=
      isCompact_Icc.image_of_continuousOn (hcont.mono (fun _ hx => hx.1))
    have hdis : Disjoint ((fun z : UpperPlane => z.1) '' K)
        ((Target.trace κ b) '' Icc 0 ((T:ℝ)/κ)) := by
      rw [Set.disjoint_left]
      rintro _ ⟨z,hz,rfl⟩ htrz
      exact haway z hz htrz
    obtain ⟨ε,hε,hsep⟩ := Metric.exists_pos_forall_lt_edist
      (hK.image continuous_subtype_val) htr.isClosed hdis
    filter_upwards [level_near_trace κ hκ b hb T zlo.1.im zhi.1.im C ε
      zlo.2 zhi.2 hC (by exact_mod_cast hε)] with j hj
    intro z hz τ hτ v
    by_contra! hangle
    have hd := hj z (hmin hz) (hmax hz) hτ hangle
    have hτf : τ≠∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hτ
    have htT : τ.toNNReal≤T := ENNReal.coe_le_coe.mp (by
      simpa only [ENNReal.coe_toNNReal hτf] using hτ)
    have httr : Target.trace κ b ((τ.toNNReal:ℝ)/κ)∈
        (Target.trace κ b) '' Icc 0 ((T:ℝ)/κ) :=
      ⟨_,⟨by positivity,div_le_div_of_nonneg_right (show (τ.toNNReal:ℝ)≤T from htT) hκ.le⟩,rfl⟩
    have hh := hsep z.1 ⟨z,hz,rfl⟩ _ httr
    rw [edist_nndist,ENNReal.coe_lt_coe] at hh
    exact (not_lt_of_ge (le_of_lt (show (ε:ℝ)<dist z.1
      (Target.trace κ b ((τ.toNNReal:ℝ)/κ)) from hh))) hd
  · exact Eventually.of_forall (fun _ z hz => False.elim (hne ⟨z,hz⟩))

lemma angleLift_ge_cot_rpow (q C : ℝ) (hq : 0≤q) (hC : 0≤C) (v : State)
    (hv : C≤|X v/Y v|) : C^q≤angleLift (sinePower (-q)) v := by
  have hp := Real.sin_pos_of_pos_of_lt_pi (physicalTheta_mem v).1 (physicalTheta_mem v).2
  have habs : |X v/Y v|≤(Real.sin (physicalTheta v))⁻¹ := by
    rw [←physicalTheta_cot,Real.cot_eq_cos_div_sin,abs_div,abs_of_pos hp]
    simpa only [one_div] using div_le_div_of_nonneg_right
      (Real.abs_cos_le_one (physicalTheta v)) hp.le
  calc
    C^q ≤ ((Real.sin (physicalTheta v))⁻¹)^q := Real.rpow_le_rpow hC (hv.trans habs) hq
    _ = angleLift (sinePower (-q)) v := by
      simp only [angleLift,sinePower,Real.rpow_neg_eq_inv_rpow]

 
lemma timeMassDensity_le_angular (κ q C : ℝ) (hq : 0≤q) (hC : 0<C)
    (b : TDriver) (T : ℝ≥0) (j : ℕ) (z : UpperPlane)
    (hangle :
      let τ := radialTime (Target.a κ) (driverHomeomorph b).1 z.1
        (z.1.im*Real.exp (-2*(Target.a κ)*(j+1)))
      τ≤(T:ℝ≥0∞) →
      let v := actualState (Target.a κ) (driverHomeomorph b).1 τ.toNNReal z.1
      C≤|X v/Y v|) :
    timeMassDensity (Target.a κ) (Real.exp (-2*(Target.a κ)*(j+1))) T
      (driverHomeomorph b) z.1 ≤
      ENNReal.ofReal (C^(-q))*angularDensity (Target.a κ) q j (driverHomeomorph b) z := by
  let τ := radialTime (Target.a κ) (driverHomeomorph b).1 z.1
    (z.1.im*Real.exp (-2*(Target.a κ)*(j+1)))
  by_cases hτ : τ≤(T:ℝ≥0∞)
  · have hτf : τ≠∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hτ
    let v := actualState (Target.a κ) (driverHomeomorph b).1 τ.toNNReal z.1
    have hF := angleLift_ge_cot_rpow q C hq hC.le v (hangle hτ)
    have hpow : 0<C^(-q) := Real.rpow_pos_of_pos hC _
    have hprod : C^(-q)*C^q=1 := by
      rw [Real.rpow_neg hC.le,inv_mul_cancel₀ (Real.rpow_pos_of_pos hC q).ne']
    have hmul : 1≤C^(-q)*angleLift (sinePower (-q)) v := by
      rw [←hprod]
      exact mul_le_mul_of_nonneg_left hF hpow.le
    have hnorm : 2*z.1.im*Real.exp (-2*Target.a κ*(j+1))/2=
        z.1.im*Real.exp (-2*Target.a κ*(j+1)) := by ring
    have hrad : levelRadius (Target.a κ) (2*z.1.im) (j+1)=
        z.1.im*Real.exp (-2*Target.a κ*(j+1)) := by simp [levelRadius]
    simp only [timeMassDensity,show radialTime (Target.a κ) (driverHomeomorph b).1 z.1
      (z.1.im*Real.exp (-2*Target.a κ*(j+1)))≤(T:ℝ≥0∞) from hτ,ite_true,
      massDensity,z.2,fullRadialDensity,hnorm,radialWeight,
      show radialTime (Target.a κ) (driverHomeomorph b).1 z.1
        (z.1.im*Real.exp (-2*Target.a κ*(j+1)))≠∞ from hτf,ite_false,
      angularDensity,hrad,radialTestWeight]
    rw [←ENNReal.ofReal_mul hpow.le]
    apply ENNReal.ofReal_le_ofReal
    have hg : 0≤Real.exp (-alpha (Target.a κ)*Real.log 2)*physicalGreen (Target.a κ) v :=
      mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    convert mul_le_mul_of_nonneg_left hmul hg using 1 <;> first | rfl | (dsimp only [v,τ]; ring)
  · simp only [timeMassDensity,show ¬radialTime (Target.a κ) (driverHomeomorph b).1 z.1
      (z.1.im*Real.exp (-2*Target.a κ*(j+1)))≤(T:ℝ≥0∞) from hτ,ite_false,zero_le]

lemma actualUpperMass_ofReal_integral (a r : ℝ) (ha : 1/4<a)
    (hr : 0<r) (hr1 : r≤1) (T : ℝ≥0∞) (b : ExactSLEGenerator.Driver)
    (f : C_c(UpperPlane,ℝ)) (hf : ∀z,0≤f z) :
    ENNReal.ofReal (∫z,f z∂actualUpperMass a r T b)=
      ∫⁻z, timeMassDensity a r T b z.1*ENNReal.ofReal (f z)∂upperArea := by
  let := actualUpperMass_finiteOnCompacts a ha r hr hr1 T b
  have hm : Measurable (fun z : UpperPlane => timeMassDensity a r T b z.1) :=
    (timeMassDensity_measurable a ha r hr hr1 T).comp
      (measurable_const.prodMk measurable_subtype_coe)
  rw [ofReal_integral_eq_lintegral_ofReal f.integrable (Eventually.of_forall hf),
    actualUpperMass,lintegral_withDensity_eq_lintegral_mul upperArea hm
      (g := fun z => ENNReal.ofReal (f z)) f.continuous.measurable.ennreal_ofReal]
  rfl

lemma angularCompactMass_const_mul (a q : ℝ) (ha : 1/4<a) (j : ℕ)
    (b : ExactSLEGenerator.Driver) (K : Set UpperPlane) (hK : MeasurableSet K)
    (C : ℝ≥0∞) :
    C*angularCompactMass a q j K b=
      ∫⁻z, K.indicator (fun z => C*angularDensity a q j b z) z∂upperArea := by
  have hm : Measurable (fun z : UpperPlane => angularDensity a q j b z) :=
    (angularDensity_measurable a q ha j).comp (measurable_const.prodMk measurable_id)
  rw [angularCompactMass,lintegral_indicator hK,lintegral_const_mul C hm]

 

lemma actualUpperMass_integral_le_angular (κ q C B : ℝ) (ha : 1/4<Target.a κ)
    (hq : 0≤q) (hC : 0<C) (hB : 0≤B) (b : TDriver) (T : ℝ≥0)
    (j : ℕ) (K : Set UpperPlane) (hK : MeasurableSet K)
    (f : C_c(UpperPlane,ℝ)) (hf : ∀ z,0≤f z) (hfK : tsupport f⊆K)
    (hfB : ∀ z∈tsupport f,f z≤B)
    (hangle : ∀ z∈tsupport f,
      let τ := radialTime (Target.a κ) (driverHomeomorph b).1 z.1
        (z.1.im*Real.exp (-2*(Target.a κ)*(j+1)))
      τ≤(T:ℝ≥0∞) →
      let v := actualState (Target.a κ) (driverHomeomorph b).1 τ.toNNReal z.1
      C≤|X v/Y v|) :
    ENNReal.ofReal (∫z,f z∂actualUpperMass (Target.a κ)
        (Real.exp (-2*(Target.a κ)*(j+1))) T (driverHomeomorph b))≤
      ENNReal.ofReal (B*C^(-q))*angularCompactMass (Target.a κ) q j K (driverHomeomorph b) := by
  rw [actualUpperMass_ofReal_integral (Target.a κ) _ ha (Real.exp_pos _)
      (level_step_lt_one (Target.a κ) ha j).le T (driverHomeomorph b) f hf,
    angularCompactMass_const_mul (Target.a κ) q ha j (driverHomeomorph b) K hK]
  apply lintegral_mono
  intro z
  by_cases hz : z∈tsupport f
  · rw [Set.indicator_of_mem (hfK hz)]
    change timeMassDensity (Target.a κ) (Real.exp (-2*(Target.a κ)*(j+1))) T
      (driverHomeomorph b) z.1*ENNReal.ofReal (f z)≤_
    calc
      _ ≤ (ENNReal.ofReal (C^(-q))*angularDensity (Target.a κ) q j (driverHomeomorph b) z)*
          ENNReal.ofReal B :=
        mul_le_mul' (timeMassDensity_le_angular κ q C hq hC b T j z (hangle z hz))
          (ENNReal.ofReal_le_ofReal (hfB z hz))
      _ = _ := by rw [ENNReal.ofReal_mul hB]; ac_rfl
  · simp only [image_eq_zero_of_notMem_tsupport hz,ENNReal.ofReal_zero,
      mul_zero,zero_le]

 

theorem actual_limit_integral_zero_away_trace (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (q : ℝ) (hq : 0<q) (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ)
    (hc : ∀ k j,j∈s k→0≤c k j) (hs : ∀ k j,j∈s k→k≤j)
    (b : TDriver) (hb : AngularRegular κ b)
    (hcont : ContinuousOn (Target.trace κ b) (Ici 0)) (T : ℝ≥0)
    (K : Set UpperPlane) (hK : MeasurableSet K)
    (f : C_c(UpperPlane,ℝ)) (hf : ∀z,0≤f z) (hfK : tsupport f⊆K)
    (haway : ∀ z∈tsupport f,z.1∉(Target.trace κ b) '' Icc 0 ((T:ℝ)/κ))
    (μ : Measure UpperPlane)
    (hlim : Tendsto (fun k => ∑ j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
        (Real.exp (-2*(Target.a κ)*(j+1))) T (driverHomeomorph b)) atTop (𝓝 (∫z,f z∂μ)))
    (hangular : liminf (fun k => convexAngularMass (Target.a κ) q (s k) (c k) K
        (driverHomeomorph b)) atTop<∞) : (∫z,f z∂μ)=0 := by
  obtain ⟨B,hB⟩ := f.hasCompactSupport.bddAbove_image f.continuous.continuousOn
  let D : ℝ := max 0 B
  have hD : 0≤D := le_max_left _ _
  have hDf : ∀ z∈tsupport f,f z≤D := fun z hz => (hB ⟨z,hz,rfl⟩).trans (le_max_right _ _)
  obtain ⟨L,hL,_⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hangular
  have hfreq := Filter.frequently_lt_of_liminf_lt (h := hL)
  have hbound (C : ℝ) (hC : 0<C) : ENNReal.ofReal (∫z,f z∂μ)≤
      ENNReal.ofReal (D*C^(-q))*(L:ℝ≥0∞) := by
    obtain ⟨N,hN⟩ := eventually_atTop.mp (compact_away_angle_large κ hκ b hb hcont T
      (tsupport f) f.hasCompactSupport haway C hC.le)
    have hev : ∀ᶠ k : ℕ in atTop,
        ENNReal.ofReal (∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
          (Real.exp (-2*(Target.a κ)*(j+1))) T (driverHomeomorph b))≤
        ENNReal.ofReal (D*C^(-q))*convexAngularMass (Target.a κ) q (s k) (c k) K
          (driverHomeomorph b) := by
      filter_upwards [eventually_ge_atTop N] with k hk
      rw [ENNReal.ofReal_sum_of_nonneg (fun j hj => mul_nonneg (hc k j hj) (integral_nonneg hf)),
        convexAngularMass,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      rw [ENNReal.ofReal_mul (hc k j hj)]
      have hbj := actualUpperMass_integral_le_angular κ q C D
        (TraceMassIntegration.a_gt_quarter hκ hκ8) hq.le hC hD b T j K hK f hf hfK hDf
        (fun z hz hτ => (hN j (hk.trans (hs k j hj)) z hz hτ).le)
      exact (mul_le_mul' le_rfl hbj).trans_eq (by ac_rfl)
    apply le_of_tendsto_of_frequently (ENNReal.tendsto_ofReal hlim)
    exact (hfreq.and_eventually hev).mono (fun k hk => hk.2.trans (mul_le_mul' le_rfl hk.1.le))
  have hdecay : Tendsto (fun C : ℝ => ENNReal.ofReal ((D*C^(-q))*(L:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (((tendsto_rpow_neg_atTop hq).const_mul D).mul_const (L:ℝ))
  have hz : ENNReal.ofReal (∫z,f z∂μ)≤0 := by
    apply ge_of_tendsto hdecay
    filter_upwards [eventually_gt_atTop (0:ℝ)] with C hC
    rw [ENNReal.ofReal_mul (mul_nonneg hD (Real.rpow_pos_of_pos hC _).le),ENNReal.ofReal_coe_nnreal]
    exact hbound C hC
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp (le_antisymm hz bot_le)) (integral_nonneg hf)

end SLEExactGauge.TraceLevelLocalization

namespace SLEExactGauge.MassVersions

 

lemma open_null_of_nonneg_compact_tests {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.Regular]
    (U : Set X) (hU : IsOpen U)
    (htest : ∀ f : C_c(X,ℝ), (∀x,0≤f x) → tsupport f⊆U → (∫x,f x∂μ)=0)
    (_hfinite : IsFiniteMeasureOnCompacts μ := by infer_instance) : μ U=0 := by
  rw [hU.measure_eq_iSup_isCompact]
  simp only [ENNReal.iSup_eq_zero]
  intro K hKU hK
  obtain ⟨f,hfK,hfc,hfU,hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  let g : C_c(X,ℝ) := ⟨f,hfc⟩
  have hz : (fun x => f x)=ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg
    (fun x => (hf01 x).1) (f.continuous.integrable_of_hasCompactSupport hfc)).mp
      (htest g (fun x => (hf01 x).1) hfU)
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hz] with x hx hKx
  have he := hfK hKx
  change f x=0 at hx
  change f x=1 at he
  linarith

end SLEExactGauge.MassVersions

namespace SLEExactGauge.TraceLevelLocalization
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen

 

theorem actual_limit_past_trace_support (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (q : ℝ) (hq : 0<q) (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ)
    (hc : ∀ k j,j∈s k→0≤c k j) (hs : ∀ k j,j∈s k→k≤j)
    (b : TDriver) (hb : AngularRegular κ b)
    (hcont : ContinuousOn (Target.trace κ b) (Ici 0))
    (K : CompactExhaustion UpperPlane)
    (hangular : ∀ n,liminf (fun k => convexAngularMass (Target.a κ) q (s k) (c k) (K n)
        (driverHomeomorph b)) atTop<∞)
    (T : ℝ≥0) (μ : Measure UpperPlane) [μ.Regular]
    (hlim : ∀ f : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
        (Real.exp (-2*(Target.a κ)*(j+1))) T (driverHomeomorph b)) atTop (𝓝 (∫z,f z∂μ)))
    (_hfinite : IsFiniteMeasureOnCompacts μ := by infer_instance) :
    μ {z : UpperPlane | z.1∉(Target.trace κ b) '' Icc 0 ((T:ℝ)/κ)}=0 := by
  have htr : IsCompact ((Target.trace κ b) '' Icc 0 ((T:ℝ)/κ)) :=
    isCompact_Icc.image_of_continuousOn (hcont.mono (fun _ hx => hx.1))
  apply MassVersions.open_null_of_nonneg_compact_tests μ _
    (htr.isClosed.isOpen_compl.preimage continuous_subtype_val)
  intro f hf hfU
  obtain ⟨n,hn⟩ := K.exists_superset_of_isCompact f.hasCompactSupport
  exact actual_limit_integral_zero_away_trace κ hκ hκ8 q hq s c hc hs b hb hcont T
    (K n) (K.isCompact n).measurableSet f hf hn hfU μ (hlim f) (hangular n)

end SLEExactGauge.TraceLevelLocalization
end
end
 

 
section
 
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerScaling
open ExactSLEGreen

 
def upperDilation (c : ℝ≥0) (hc : 0<c) : UpperPlane ≃ₜ UpperPlane where
  toFun z := ⟨((c:ℝ):ℂ)*z.1,by
    simpa [Complex.mul_im] using mul_pos (show 0<(c:ℝ) from hc) z.2⟩
  invFun z := ⟨((c:ℝ):ℂ)⁻¹*z.1,by
    simpa [←Complex.ofReal_inv,Complex.mul_im] using
      mul_pos (inv_pos.mpr (show 0<(c:ℝ) from hc)) z.2⟩
  left_inv z := by
    apply Subtype.ext
    simp only [←mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
      (NNReal.coe_ne_zero.mpr hc.ne')),one_mul]
  right_inv z := by
    apply Subtype.ext
    simp only [←mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr
      (NNReal.coe_ne_zero.mpr hc.ne')),one_mul]
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.mul continuous_subtype_val).subtype_mk _

@[simp] lemma upperDilation_apply (c : ℝ≥0) (hc : 0<c) (z : UpperPlane) :
    (upperDilation c hc z).1=((c:ℝ):ℂ)*z.1 := rfl

@[simp] lemma upperDilation_symm_apply (c : ℝ≥0) (hc : 0<c) (z : UpperPlane) :
    ((upperDilation c hc).symm z).1=((c:ℝ):ℂ)⁻¹*z.1 := rfl

lemma upperDilation_symm (c : ℝ≥0) (hc : 0<c) :
    (upperDilation c hc).symm=upperDilation c⁻¹ (inv_pos.mpr hc) := by
  ext z
  simp

lemma map_upperArea (c : ℝ≥0) (hc : 0<c) :
    upperArea.map (upperDilation c hc)=(c:ℝ≥0∞)⁻¹^2 • upperArea := by
  let f : ℂ → ℂ := fun z => ((c:ℝ):ℂ)*z
  have hf : Measurable f := (continuous_const.mul continuous_id).measurable
  have hpre : f ⁻¹' {z : ℂ | 0<z.im}={z : ℂ | 0<z.im} := by
    ext z
    simp only [mem_preimage,mem_ofPred_eq,f,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,add_zero]
    exact mul_pos_iff_of_pos_left (show 0<(c:ℝ) from hc)
  have hmap : (volume : Measure ℂ).map f=(c:ℝ≥0∞)⁻¹^2 • volume := by
    have hm := Measure.map_addHaar_smul (volume : Measure ℂ)
      (show (c:ℝ)≠0 from NNReal.coe_ne_zero.mpr hc.ne')
    simpa only [Complex.real_smul,Complex.finrank_real_complex,abs_of_nonneg
      (inv_nonneg.mpr (sq_nonneg (c:ℝ))),
      ENNReal.ofReal_inv_of_pos (sq_pos_of_pos (show 0<(c:ℝ) from hc)),
      ENNReal.ofReal_pow c.coe_nonneg,ENNReal.ofReal_coe_nnreal,ENNReal.inv_pow,f] using hm
  apply upper_embedding.map_injective
  calc
    (upperArea.map (upperDilation c hc)).map Subtype.val =
        (upperArea.map (Subtype.val : UpperPlane → ℂ)).map f := by
      rw [Measure.map_map measurable_subtype_coe (upperDilation c hc).measurable,
        Measure.map_map hf measurable_subtype_coe]
      rfl
    _ = ((volume : Measure ℂ).restrict {z | 0<z.im}).map f := by
      rw [upperArea,upper_embedding.map_comap,Subtype.range_val_subtype]
    _ = ((volume : Measure ℂ).map f).restrict {z | 0<z.im} := by
      rw [Measure.restrict_map hf upperPlane_open.measurableSet,hpre]
    _ = ((c:ℝ≥0∞)⁻¹^2 • upperArea).map Subtype.val := by
      rw [hmap,Measure.map_smul _ measurable_subtype_coe.aemeasurable,
        upperArea,upper_embedding.map_comap,Measure.restrict_smul,
        Subtype.range_val_subtype]

 
lemma map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (f : Y → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (fun x => f (e x))).map e=(μ.map e).withDensity f := by
  ext A hA
  rw [Measure.map_apply e.measurable hA,withDensity_apply _ (e.measurable hA),
    withDensity_apply _ hA,Measure.restrict_map e.measurable hA,
    lintegral_map hf e.measurable]

end SLEExactGauge.LoewnerScaling
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerScaling
open ExactSLEMain ExactSLEGreen

lemma scaling_factor (a : ℝ) {c : ℝ≥0} (hc : 0<c) :
    ENNReal.ofReal ((c:ℝ)^(alpha a))*(c:ℝ≥0∞)⁻¹^2 =
      ENNReal.ofReal ((c:ℝ)^(alpha a-2)) := by
  rw [Real.rpow_sub (show 0<(c:ℝ) from hc),Real.rpow_two,
    ENNReal.ofReal_div_of_pos (sq_pos_of_pos (show 0<(c:ℝ) from hc)),
    ENNReal.ofReal_pow c.coe_nonneg,ENNReal.ofReal_coe_nnreal,div_eq_mul_inv,ENNReal.inv_pow]

lemma map_actualUpperMass_scaled (a : ℝ) (ha : 1/4<a) {c : ℝ≥0} (hc : 0<c)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1) (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) :
    (actualUpperMass a q t (scaleDriver c b)).map (upperDilation c hc) =
      ENNReal.ofReal ((c:ℝ)^(alpha a-2)) • actualUpperMass a q ((c:ℝ≥0∞)^2*t) b := by
  let e := upperDilation c hc
  let f : UpperPlane → ℝ≥0∞ := fun z => timeMassDensity a q ((c:ℝ≥0∞)^2*t) b z.1
  have hf : Measurable f := (timeMassDensity_measurable a ha q hq hq1 _).comp
    (measurable_const.prodMk measurable_subtype_coe)
  have he : (fun z : UpperPlane => timeMassDensity a q t (scaleDriver c b) z.1) =
      fun z => ENNReal.ofReal ((c:ℝ)^(alpha a))*f (e z) := by
    funext z
    exact timeMassDensity_scaled_upper a (by linarith) hc q hq hq1 t b z.1 z.2
  simp only [actualUpperMass,he]
  rw [show (fun z => ENNReal.ofReal ((c:ℝ)^(alpha a))*f (e z)) =
    ENNReal.ofReal ((c:ℝ)^(alpha a)) • (fun z => f (e z)) from rfl,
    withDensity_smul' _ _ ENNReal.ofReal_ne_top,
    Measure.map_smul _ (upperDilation c hc).measurable.aemeasurable]
  have hmf : (upperArea.withDensity (fun z => f (e z))).map e =
      (upperArea.map e).withDensity f := map_withDensity_comp e.toMeasurableEquiv upperArea f hf
  rw [hmf,map_upperArea c hc,withDensity_smul_measure,smul_smul,scaling_factor a hc]

lemma map_actualConvexMass_scaled (a : ℝ) (ha : 1/4<a) {c : ℝ≥0} (hc : 0<c)
    (s : Finset ℕ) (v : ℕ → ℝ) (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) :
    (actualConvexMass a s v t (scaleDriver c b)).map (upperDilation c hc) =
      ENNReal.ofReal ((c:ℝ)^(alpha a-2)) • actualConvexMass a s v ((c:ℝ≥0∞)^2*t) b := by
  simp only [actualConvexMass,Measure.map_finset_sum (upperDilation c hc).measurable.aemeasurable,
    Measure.map_smul _ (upperDilation c hc).measurable.aemeasurable,
    map_actualUpperMass_scaled a ha hc _ (Real.exp_pos _) (level_step_le_one a ha _),
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact smul_comm _ _ _

end SLEExactGauge.LoewnerScaling
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.MassVersions

variable {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [T2Space Y] [LocallyCompactSpace Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] in
lemma compact_comp_symm_comp [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (e : X ≃ₜ Y) (f : C_c(X,ℝ)) :
    (f.comp e.symm.toCocompactMap).comp e.toCocompactMap=f := by
  ext x
  exact congrArg f (e.symm_apply_apply x)

lemma testConverges_equiv (e : X ≃ₜ Y) {r : ℝ} (hr : 0<r)
    (L : ℕ → (C_c(X,ℝ) →ₚ[ℝ] ℝ)) (R : ℕ → (C_c(Y,ℝ) →ₚ[ℝ] ℝ))
    (h : ∀ k (f : C_c(Y,ℝ)), L k (f.comp e.toCocompactMap)=r*R k f) :
    TestConverges L ↔ TestConverges R := by
  constructor
  · intro hL i
    have ht := (tendsto_radonLimit L hL
      ((determiningTests i).comp e.toCocompactMap)).const_mul r⁻¹
    simp only [h,←mul_assoc,inv_mul_cancel₀ hr.ne',one_mul] at ht
    exact ⟨_,ht⟩
  · intro hR i
    have hb (k : ℕ) : L k (determiningTests i)=
        r*R k ((determiningTests i).comp e.symm.toCocompactMap) := by
      simpa only [compact_comp_symm_comp] using h k
        ((determiningTests i).comp e.symm.toCocompactMap)
    refine ⟨r * ∫ y, ((determiningTests i).comp e.symm.toCocompactMap) y ∂radonLimit R,?_⟩
    simpa only [hb] using (tendsto_radonLimit R hR
      ((determiningTests i).comp e.symm.toCocompactMap)).const_mul r

 

theorem radonLimit_equiv (e : X ≃ₜ Y) {r : ℝ} (hr : 0<r)
    (L : ℕ → (C_c(X,ℝ) →ₚ[ℝ] ℝ)) (R : ℕ → (C_c(Y,ℝ) →ₚ[ℝ] ℝ))
    (h : ∀ k (f : C_c(Y,ℝ)), L k (f.comp e.toCocompactMap)=r*R k f) :
    (radonLimit L).map e=ENNReal.ofReal r • radonLimit R := by
  classical
  by_cases hR : TestConverges R
  · have hL := (testConverges_equiv e hr L R h).mpr hR
    let := radonLimit_regular L
    let := radonLimit_regular R
    let : ((radonLimit L).map e).Regular := Measure.Regular.map e
    let : (ENNReal.ofReal r • radonLimit R).Regular :=
      Measure.Regular.smul ENNReal.ofReal_ne_top
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_smul_measure,ENNReal.toReal_ofReal hr.le,smul_eq_mul]
    rw [show (∫ y,f y ∂(radonLimit L).map e) =
      ∫ x,(f.comp e.toCocompactMap) x ∂radonLimit L from
      integral_map_equiv e.toMeasurableEquiv f]
    apply tendsto_nhds_unique (tendsto_radonLimit L hL (f.comp e.toCocompactMap))
    simpa only [h] using (tendsto_radonLimit R hR f).const_mul r
  · have hL := (testConverges_equiv e hr L R h).not.mpr hR
    simp only [radonLimit,dite_eq_right hL,dite_eq_right hR,Measure.map_zero,smul_zero]

end SLEExactGauge.MassVersions
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerScaling
open ExactSLEMain ExactSLEGreen SLEExactGauge.MassVersions

lemma actualMassFunctionals_integral (a : ℝ) (ha : 1/4<a)
    (s : ℕ → Finset ℕ) (v : ℕ → ℕ → ℝ) (hv : ∀ k j, j∈s k → 0≤v k j)
    (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) (k : ℕ) (f : C_c(UpperPlane,ℝ)) :
    actualMassFunctionals a ha s v hv t b k f = ∫ z,f z ∂actualConvexMass a (s k) (v k) t b := by
  rw [actualMassFunctionals_apply,actualConvexMass_integral a ha _ _ (hv k)]

lemma actualMassFunctionals_scaled (a : ℝ) (ha : 1/4<a) {c : ℝ≥0} (hc : 0<c)
    (s : ℕ → Finset ℕ) (v : ℕ → ℕ → ℝ) (hv : ∀ k j, j∈s k → 0≤v k j)
    (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) (k : ℕ) (f : C_c(UpperPlane,ℝ)) :
    actualMassFunctionals a ha s v hv t (scaleDriver c b) k
      (f.comp (upperDilation c hc).toCocompactMap) =
    (c:ℝ)^(alpha a-2)* actualMassFunctionals a ha s v hv ((c:ℝ≥0∞)^2*t) b k f := by
  simp only [actualMassFunctionals_integral]
  calc
    _ = ∫ z,f z ∂(actualConvexMass a (s k) (v k) t (scaleDriver c b)).map
        (upperDilation c hc) := (integral_map_equiv (upperDilation c hc).toMeasurableEquiv f).symm
    _ = _ := by
      rw [map_actualConvexMass_scaled a ha hc,integral_smul_measure,
        ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (show 0<(c:ℝ) from hc) _).le,smul_eq_mul]

 
theorem map_recoveredMass_scaled (a : ℝ) (ha : 1/4<a) {c : ℝ≥0} (hc : 0<c)
    (s : ℕ → Finset ℕ) (v : ℕ → ℕ → ℝ) (hv : ∀ k j, j∈s k → 0≤v k j)
    (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) :
    (recoveredMass a ha s v hv t (scaleDriver c b)).map (upperDilation c hc) =
      ENNReal.ofReal ((c:ℝ)^(alpha a-2)) • recoveredMass a ha s v hv ((c:ℝ≥0∞)^2*t) b := by
  apply radonLimit_equiv (upperDilation c hc)
    (Real.rpow_pos_of_pos (show 0<(c:ℝ) from hc) _) _ _
  exact actualMassFunctionals_scaled a ha hc s v hv t b

 

theorem recoveredMass_scaled (a : ℝ) (ha : 1/4<a) {c : ℝ≥0} (hc : 0<c)
    (s : ℕ → Finset ℕ) (v : ℕ → ℕ → ℝ) (hv : ∀ k j, j∈s k → 0≤v k j)
    (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) (A : Set UpperPlane) :
    recoveredMass a ha s v hv t (scaleDriver c b) A =
      ENNReal.ofReal ((c:ℝ)^(alpha a-2)) *
        recoveredMass a ha s v hv ((c:ℝ≥0∞)^2*t) b ((upperDilation c hc) '' A) := by
  have h := congrArg (fun μ : Measure UpperPlane => μ ((upperDilation c hc) '' A))
    (map_recoveredMass_scaled a ha hc s v hv t b)
  simpa only [(upperDilation c hc).measurableEmbedding.map_apply,
    Set.preimage_image_eq _ (upperDilation c hc).injective,Measure.smul_apply,smul_eq_mul] using h

lemma recoveredMass_scaled_univ_pos_iff (a : ℝ) (ha : 1/4<a) {c : ℝ≥0} (hc : 0<c)
    (s : ℕ → Finset ℕ) (v : ℕ → ℕ → ℝ) (hv : ∀ k j, j∈s k → 0≤v k j)
    (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) :
    0 < recoveredMass a ha s v hv t (scaleDriver c b) univ ↔
      0 < recoveredMass a ha s v hv ((c:ℝ≥0∞)^2*t) b univ := by
  rw [recoveredMass_scaled a ha hc s v hv t b univ,
    image_univ,range_eq_univ.mpr (upperDilation c hc).surjective]
  have hr : 0<ENNReal.ofReal ((c:ℝ)^(alpha a-2)) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (show 0<(c:ℝ) from hc) _)
  rw [ENNReal.mul_pos_iff]
  exact and_iff_right hr

 

theorem recoveredMass_positivity_probability (a : ℝ) (ha : 1/4<a)
    (s : ℕ → Finset ℕ) (v : ℕ → ℕ → ℝ) (hv : ∀ k j, j∈s k → 0≤v k j)
    (W : Measure ExactSLEGenerator.Driver)
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (u t : ℝ≥0) (hu : 0<u) (ht : 0<t) :
    W {b | 0<recoveredMass a ha s v hv u b univ}=
      W {b | 0<recoveredMass a ha s v hv t b univ} := by
  let c := NNReal.sqrt (t/u)
  have hc : 0<c := NNReal.sqrt_pos.mpr (div_pos ht hu)
  have hcu : c^2*u=t := by
    dsimp only [c]
    rw [NNReal.sq_sqrt,div_mul_cancel₀ _ hu.ne']
  have hcu' : (c:ℝ≥0∞)^2*(u:ℝ≥0∞)=(t:ℝ≥0∞) := by exact_mod_cast hcu
  let E := {b | 0<recoveredMass a ha s v hv u b univ}
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    ((Measure.measurable_coe MeasurableSet.univ).comp (recoveredMass_measurable a ha s v hv u))
  calc
    _ = W ((scaleDriver c) ⁻¹' E) := by
      exact ((measurePreserving_scaleDriver hW hc).measure_preimage hE.nullMeasurableSet).symm
    _ = _ := by
      apply congrArg (fun A : Set ExactSLEGenerator.Driver => W A)
      apply Set.ext
      intro b
      change (0<recoveredMass a ha s v hv u (scaleDriver c b) univ) ↔ _
      rw [recoveredMass_scaled_univ_pos_iff a ha hc s v hv u b,hcu']
      rfl

end SLEExactGauge.LoewnerScaling
end
end

end OAI
