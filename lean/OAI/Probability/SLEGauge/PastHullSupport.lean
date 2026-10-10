import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.HeightRadius
import OAI.Probability.SLEGauge.AngularControlMass

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

lemma fullLoewnerRadius_continuousOn (a : ℝ) (b : ExactSLEGenerator.Driver) (t : ℝ≥0) :
    ContinuousOn (fun z => fullLoewnerRadius a b.1 z t) {z | alive a b.1 t z} := by
  have hd : DifferentiableOn ℂ (loewnerMap a b.1 t) {z | alive a b.1 t z} :=
    fun _ hz => (hasDerivAt_loewnerMap b.1.continuous hz).differentiableAt.differentiableWithinAt
  have hc := hd.continuousOn
  exact (continuousOn_const.mul (Complex.continuous_im.comp_continuousOn hc)).div
    ((hd.analyticOnNhd (isOpen_alive b.1.continuous t)).deriv.continuousOn.norm)
    (fun z hz => norm_ne_zero_iff.mpr (deriv_loewnerMap_ne_zero b.1.continuous hz))

lemma physicalRadius_actual_continuousOn (a : ℝ) (b : ExactSLEGenerator.Driver) (t : ℝ≥0) :
    ContinuousOn (fun z => physicalRadius (actualState a b.1 t z)) {z | alive a b.1 t z} := by
  have hc := (fullLoewnerRadius_continuousOn a b t).div_const 2
  apply hc.congr
  intro z hz
  have he := actual_radius_eq_full b.1.continuous hz
  linarith

 

lemma surviving_compact_radius_margin (a : ℝ) (b : ExactSLEGenerator.Driver) (t : ℝ≥0)
    (K : Set UpperPlane) (hK : IsCompact K)
    (hKs : ∀ z∈K, alive a b.1 t z.1) :
    ∃ ε : ℝ, 0<ε ∧ ∀ z∈K, ε≤physicalRadius (actualState a b.1 t z.1)/z.1.im := by
  by_cases hne : K.Nonempty
  · have hc : ContinuousOn (fun z : UpperPlane =>
        physicalRadius (actualState a b.1 t z.1)/z.1.im) K := by
      apply ContinuousOn.div
        ((physicalRadius_actual_continuousOn a b t).comp continuous_subtype_val.continuousOn hKs)
        (Complex.continuous_im.comp continuous_subtype_val).continuousOn
      exact fun z _ => z.2.ne'
    obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn hne hc
    exact ⟨_,div_pos (physicalRadius_actual_pos a b z.1 t (hKs z hz)) z.2,
      fun w hw => hmin hw⟩
  · exact ⟨1,zero_lt_one,fun z hz => False.elim (hne ⟨z,hz⟩)⟩

lemma timeMassDensity_zero_of_radius_lt (a : ℝ) (ha : 0<a) (b : ExactSLEGenerator.Driver)
    (t : ℝ≥0) (z : UpperPlane) (ht : alive a b.1 t z.1)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (hqr : z.1.im*q<physicalRadius (actualState a b.1 t z.1)) :
    timeMassDensity a q t b z.1=0 := by
  have hn : ¬radialTime a b.1 z.1 (z.1.im*q)≤(t : ℝ≥0∞) := by
    intro hle
    have hfin : radialTime a b.1 z.1 (z.1.im*q)≠∞ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top hle
    have htt : (radialTime a b.1 z.1 (z.1.im*q)).toNNReal≤t :=
      ENNReal.coe_le_coe.mp (by simpa only [ENNReal.coe_toNNReal hfin] using hle)
    have he := (radialTime_attained a ha z.1 z.2 _ (mul_pos z.2 hq)
      (mul_le_of_le_one_right z.2.le hq1) b hfin).2
    have hr := physicalRadius_actual_anti a ha b z.1 _ t htt ht
    rw [he] at hr
    exact (not_le_of_gt hqr) hr
  exact ite_eq_right hn

lemma timeMassDensity_eventually_zero_on_surviving_compact (a : ℝ) (ha : 0<a)
    (b : ExactSLEGenerator.Driver) (t : ℝ≥0) (K : Set UpperPlane) (hK : IsCompact K)
    (hKs : ∀ z∈K, alive a b.1 t z.1)
    (q : ℕ → ℝ) (hq : ∀ j, 0<q j ∧ q j≤1) (hlim : Tendsto q atTop (𝓝 0)) :
    ∀ᶠ j in atTop, ∀ z∈K, timeMassDensity a (q j) t b z.1=0 := by
  obtain ⟨ε,hε,hεK⟩ := surviving_compact_radius_margin a b t K hK hKs
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with j hj
  intro z hz
  exact timeMassDensity_zero_of_radius_lt a ha b t z (hKs z hz) (q j) (hq j).1 (hq j).2
    (by simpa only [mul_comm] using (lt_div_iff₀ z.2).mp (hj.trans_le (hεK z hz)))

lemma actualUpperMass_eval_eventually_zero_on_surviving (a : ℝ) (ha : 1/4<a)
    (b : ExactSLEGenerator.Driver) (t : ℝ≥0) (f : C_c(UpperPlane,ℝ))
    (hf : ∀ z∈tsupport f, alive a b.1 t z.1)
    (q : ℕ → ℝ) (hq : ∀ j, 0<q j ∧ q j≤1) (hlim : Tendsto q atTop (𝓝 0)) :
    ∀ᶠ j in atTop, (∫z,f z∂actualUpperMass a (q j) t b)=0 := by
  filter_upwards [timeMassDensity_eventually_zero_on_surviving_compact a (by linarith)
    b t (tsupport f) f.hasCompactSupport hf q hq hlim] with j hj
  have hm : Measurable (fun z : UpperPlane => timeMassDensity a (q j) t b z.1) :=
    (timeMassDensity_measurable a ha (q j) (hq j).1 (hq j).2 t).comp
      (measurable_const.prodMk measurable_subtype_coe)
  rw [actualUpperMass,integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall (fun z => timeMassDensity_finite a (q j) t b z.1))]
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro z
  by_cases hz : z∈tsupport f
  · simp only [hj z hz,ENNReal.toReal_zero,zero_smul,Pi.zero_apply]
  · simp only [image_eq_zero_of_notMem_tsupport hz,smul_zero,Pi.zero_apply]

lemma mass_levels_tendsto_zero (a : ℝ) (ha : 0<a) :
    Tendsto (fun j : ℕ => Real.exp (-2*a*(j+1))) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  apply Tendsto.const_mul_atTop_of_neg (by linarith : -2*a<0)
  apply Filter.tendsto_atTop.mpr
  intro B
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
    (eventually_ge_atTop B)] with n hn
  linarith

 

lemma actual_limit_integral_zero_on_surviving (a : ℝ) (ha : 1/4<a)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (hs : ∀ k j, j∈s k → k≤j)
    (b : ExactSLEGenerator.Driver) (t : ℝ≥0) (μ : Measure UpperPlane)
    (f : C_c(UpperPlane,ℝ)) (hf : ∀ z∈tsupport f, alive a b.1 t z.1)
    (hlim : Tendsto (fun k => ∑ j∈s k, c k j * ∫z,f z∂actualUpperMass a
      (Real.exp (-2*a*(j+1))) t b) atTop (𝓝 (∫z,f z∂μ))) :
    (∫z,f z∂μ)=0 := by
  have hq (j : ℕ) : 0<Real.exp (-2*a*(j+1)) ∧ Real.exp (-2*a*(j+1))≤1 :=
    ⟨Real.exp_pos _,(level_step_lt_one a ha j).le⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp (actualUpperMass_eval_eventually_zero_on_surviving
    a ha b t f hf _ hq (mass_levels_tendsto_zero a (by linarith)))
  apply tendsto_nhds_unique hlim
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with k hk
  symm
  apply Finset.sum_eq_zero
  intro j hj
  rw [hN j (hk.trans (hs k j hj)),mul_zero]

end ExactSLEGreen
namespace SLEExactGauge.MassVersions

 

lemma open_null_of_compact_tests {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.Regular]
    (U : Set X) (hU : IsOpen U)
    (htest : ∀ f : C_c(X,ℝ), tsupport f⊆U → (∫x,f x∂μ)=0)
    (_hfinite : IsFiniteMeasureOnCompacts μ := by infer_instance) : μ U=0 := by
  rw [hU.measure_eq_iSup_isCompact]
  simp only [ENNReal.iSup_eq_zero]
  intro K hKU hK
  obtain ⟨f,hfK,hfc,hfU,hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  let g : C_c(X,ℝ) := ⟨f,hfc⟩
  have hz : (fun x => f x)=ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg
    (fun x => (hf01 x).1) (f.continuous.integrable_of_hasCompactSupport hfc)).mp
      (htest g hfU)
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hz] with x hx hKx
  have he := hfK hKx
  change f x=0 at hx
  change f x=1 at he
  linarith

end SLEExactGauge.MassVersions
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

 

theorem actual_limit_past_hull_support (a : ℝ) (ha : 1/4<a)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (hs : ∀ k j, j∈s k → k≤j)
    (b : ExactSLEGenerator.Driver) (t : ℝ≥0) (μ : Measure UpperPlane)
    [μ.Regular]
    (hlim : ∀ f : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑ j∈s k, c k j * ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) t b)
        atTop (𝓝 (∫z,f z∂μ)))
    (_hfinite : IsFiniteMeasureOnCompacts μ := by infer_instance) :
    μ {z : UpperPlane | alive a b.1 t z.1}=0 := by
  apply open_null_of_compact_tests μ _ ((isOpen_alive b.1.continuous t).preimage continuous_subtype_val)
  exact fun f hf => actual_limit_integral_zero_on_surviving a ha s c hs b t μ f hf (hlim f)

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.TraceLevelLocalization
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen

 
def AngularRegular (κ : ℝ) (b : TDriver) : Prop :=
  ∀ m H : ℕ, ∀ C : ℝ, 0≤C →
    TendstoUniformlyOn
      (fun y : ℝ => fun p : ℝ×ℝ => LiteralTrace.inverseFlow κ b p.1
        (LiteralTrace.driverValue b p.1+(y:ℂ)*((p.2:ℂ)+Complex.I)))
      (fun p => LiteralTrace.trace κ b (p.1/κ)) (𝓝[>] 0)
      (Icc (1/((m:ℝ)+1)) H ×ˢ Icc (-C) C)

lemma angularRegular_ae {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8)
    {W : Measure TDriver} (hW : Target.IsWiener W) : ∀ᵐ b ∂W, AngularRegular κ b :=
  LiteralTrace.angular_uniform_all_windows hκ hκ8 hW

lemma inverse_actual_state (κ : ℝ) (b : TDriver) (z : UpperPlane)
    (t : ℝ≥0) (ht : alive (Target.a κ) (driverHomeomorph b).1 t z.1) :
    let v := actualState (Target.a κ) (driverHomeomorph b).1 t z.1
    LiteralTrace.inverseFlow κ b t
      (LiteralTrace.driverValue b t+(Y v:ℂ)*((X v/Y v:ℂ)+Complex.I))=z.1 := by
  let v := actualState (Target.a κ) (driverHomeomorph b).1 t z.1
  have hy : 0<Y v := by
    have he := (actualState_evolution (Target.a κ) (driverHomeomorph b) z t ht).yp t
      ⟨t.coe_nonneg,le_rfl⟩
    simpa only [Real.toNNReal_coe] using he
  have hs : LiteralTrace.Surviving κ b z.1 t :=
    (surviving_eq κ b z.1 t).mp ((surviving_iff_alive κ b z.1 t).mpr ht)
  have he : (LiteralTrace.driverValue b t:ℂ)+(Y v:ℂ)*((X v/Y v:ℂ)+Complex.I)=
      LiteralTrace.flow κ b z.1 t := by
    rw [←flow_eq_literal,flow_eq_loewnerMap]
    have hxy : Y v*(X v/Y v)=X v := by field_simp
    apply Complex.ext
    · simpa [v,X,Y,actualState,LiteralTrace.driverValue] using
        congrArg (fun r : ℝ => b t+r) hxy
    · simp [v,X,Y,actualState]
  change LiteralTrace.inverseFlow κ b t _=z.1
  rw [he]
  exact LiteralTrace.inverseFlow_flow t.coe_nonneg hs

 

theorem level_near_trace (κ : ℝ) (hκ : 0<κ) (b : TDriver)
    (hb : AngularRegular κ b) (T : ℝ≥0) (η M C ε : ℝ)
    (hη : 0<η) (_hM : 0<M) (hC : 0≤C) (hε : 0<ε) :
    ∀ᶠ j : ℕ in atTop, ∀ z : UpperPlane, η≤z.1.im → z.1.im≤M →
      let τ := radialTime (Target.a κ) (driverHomeomorph b).1 z.1
        (z.1.im*Real.exp (-2*(Target.a κ)*(j+1)))
      τ≤(T:ℝ≥0∞) →
      let v := actualState (Target.a κ) (driverHomeomorph b).1 τ.toNNReal z.1
      |X v/Y v|≤C →
      dist z.1 (Target.trace κ b ((τ.toNNReal:ℝ)/κ))<ε := by
  have ha : 0<Target.a κ := by dsimp [Target.a]; positivity
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt (show 0<η^2/(4*Target.a κ) by positivity)
  obtain ⟨H,hH⟩ := exists_nat_gt (T:ℝ)
  obtain ⟨δ,hδ,hδlim⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (Metric.tendstoUniformlyOn_iff.mp (hb m H C hC) ε hε)
  have hg : Tendsto (fun j : ℕ => Real.exp (-Target.a κ*(j+1))) atTop (𝓝 0) := by
    have he := mass_levels_tendsto_zero (Target.a κ/2) (by positivity)
    convert he using 1
    funext j
    congr 1
    ring
  have hg' : Tendsto (fun j : ℕ => M*Real.exp (-Target.a κ*(j+1))) atTop (𝓝 0) := by
    simpa using hg.const_mul M
  filter_upwards [(mass_levels_tendsto_zero (Target.a κ) ha).eventually
      (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)), hg'.eventually (gt_mem_nhds hδ)] with j hj hj'
  intro z hzη hzM τ hτ v hv
  have hτf : τ≠∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hτ
  have hτT : τ.toNNReal≤T := ENNReal.coe_le_coe.mp (by
    simpa only [ENNReal.coe_toNNReal hτf] using hτ)
  have hr : 0<z.1.im*Real.exp (-2*Target.a κ*(j+1)) := mul_pos z.2 (Real.exp_pos _)
  have hr2 : z.1.im*Real.exp (-2*Target.a κ*(j+1))≤z.1.im/2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hj.le z.2.le]
  have hτlower := radialTime_half_lower (Target.a κ) ha (driverHomeomorph b) z _ hr hr2 hτf
  have hτalive := (radialTime_attained (Target.a κ) ha z.1 z.2 _ hr
    (by linarith [z.2]) (driverHomeomorph b) hτf).1
  have hyp : 0<Y v := by
    simpa only [Real.toNNReal_coe] using
      (actualState_evolution (Target.a κ) (driverHomeomorph b) z τ.toNNReal hτalive).yp
        (τ.toNNReal:ℝ) ⟨τ.toNNReal.coe_nonneg,le_rfl⟩
  have hyv : Y v≤z.1.im*Real.exp (-Target.a κ*(j+1)) := by
    have hh := level_height_bound (Target.a κ) ha (driverHomeomorph b) z (j+1) (by positivity)
      (by simpa [τ,levelRadius] using hτf)
    simpa [v,τ,levelRadius] using hh
  have hyδ : Y v<δ := hyv.trans_lt ((mul_le_mul_of_nonneg_right hzM (Real.exp_pos _).le).trans_lt hj')
  have htl : 1/((m:ℝ)+1)≤(τ.toNNReal:ℝ) := by
    apply hm.le.trans
    apply le_trans _ hτlower
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hη.le hzη 2) (by positivity)
  have htu : (τ.toNNReal:ℝ)≤H := (show (τ.toNNReal:ℝ)≤T from hτT).trans hH.le
  have h := hδlim ⟨hyp,hyδ⟩ (τ.toNNReal,X v/Y v) ⟨⟨htl,htu⟩,abs_le.mp hv⟩
  simp only [Complex.ofReal_div] at h
  rw [inverse_actual_state κ b z τ.toNNReal hτalive] at h
  simpa only [trace_eq_literal,dist_comm] using h

end SLEExactGauge.TraceLevelLocalization
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.MassVersions

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

lemma sub_add_cancel_of_locally_finite (μ ν : Measure X)
    [IsFiniteMeasureOnCompacts μ] (h : μ≤ν) : ν-μ+μ=ν := by
  let K := CompactExhaustion.choice X
  apply Measure.ext_of_iUnion_eq_univ K.iUnion_eq
  intro n
  have : IsFiniteMeasure (μ.restrict (K n)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (K.isCompact n).measure_lt_top (μ := μ)⟩
  rw [Measure.restrict_add,
    Measure.restrict_sub_eq_restrict_sub_restrict (K.isCompact n).measurableSet]
  exact Measure.sub_add_cancel_of_le (Measure.restrict_mono Subset.rfl h)

lemma restriction_of_complementary_support (μ ν : Measure X)
    [IsFiniteMeasureOnCompacts μ] (h : μ≤ν) (D : Set X) (_hD : MeasurableSet D)
    (hμ : μ Dᶜ=0) (hrem : (ν-μ) D=0) : μ=ν.restrict D := by
  have hμD : μ.restrict D=μ := Measure.restrict_eq_self_of_ae_mem (by
    simpa only [mem_compl_iff,not_not] using measure_eq_zero_iff_ae_notMem.mp hμ)
  have hremD : (ν-μ).restrict D=0 := Measure.restrict_eq_zero.mpr hrem
  have he := congrArg (fun ρ : Measure X => ρ.restrict D)
    (sub_add_cancel_of_locally_finite μ ν h)
  simpa only [Measure.restrict_add,hremD,hμD,zero_add] using he

end SLEExactGauge.MassVersions

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

 

theorem actual_raw_mass_hull_accounting (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
      (hc : ∀ k j, j∈s k → 0≤c k j),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k, ∑ j∈s k, c k j=1) ∧
      let μ := recoveredMass a ha s c hc
      (∀ v b, IsFiniteMeasureOnCompacts (μ v b) ∧ (μ v b).Regular) ∧
      (∀ b, μ 0 b=0) ∧
      (∀ v, Measurable (μ v)) ∧
      IsProgressive rawFiltration (fun v : ℝ≥0 => μ v) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)) (m : ℕ),
        MemLp (fun b => ∫z,f z∂μ (t i) b) (m : ℝ≥0∞) W) ∧
      (∀ i (K : Set UpperPlane), IsCompact K → ∀ m : ℕ,
        MemLp (fun b => (μ (t i) b K).toReal) (m : ℝ≥0∞) W) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)),
        Tendsto (fun k => eLpNorm (fun b =>
          (∑ j∈s k, c k j * ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            - ∫z,f z∂μ (t i) b) 1 W) atTop (𝓝 0)) ∧
      (∀ i, t i=∞ → μ (t i) ∘ₘ W=initialGreenMeasure a) ∧
      (∀ i j (v : ℝ≥0), t i=v → t j=∞ →
        ∀ H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞,
        Measurable[(rawFiltration v).prod (inferInstance : MeasurableSpace UpperPlane)] H →
        (∫⁻b, ∫⁻z, H (b,z) ∂μ (t j) b ∂W) = (∫⁻b, ∫⁻z, H (b,z) ∂μ (t i) b ∂W) +
          ∫⁻b, ∫⁻z, H (b,z) * ENNReal.ofReal (survivingGreen a v b z.1) ∂upperArea ∂W) ∧
      ∀ᵐ b ∂W,
        (∀ i j, t i≤t j → μ (t i) b≤μ (t j) b) ∧
        (∀ i (f : C_c(UpperPlane,ℝ)),
          Tendsto (fun k => ∑ j∈s k, c k j *
            ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            atTop (𝓝 (∫z,f z∂μ (t i) b))) ∧
        (∀ i, NullSingletonClass (μ (t i) b)) ∧
        (∀ i (v : ℝ≥0), t i=v → μ (t i) b {z : UpperPlane | alive a b.1 v z.1}=0) ∧
        (∀ i j, t i≠∞ → t j=∞ →
          (μ (t j) b-μ (t i) b) {z : UpperPlane | ¬alive a b.1 (t i).toNNReal z.1}=0) ∧
        (∀ i j (v : ℝ≥0), t i=v → t j=∞ →
          μ (t i) b=(μ (t j) b).restrict {z : UpperPlane | ¬alive a b.1 v z.1}) := by
  obtain ⟨s,c,hc,hs,hsum,hμ,hzero,hmeas,hprog,hmom,hcompact,hL1,hmean,hH,hconv⟩ :=
    actual_raw_atomless_mass_endpoint a ha W hW t
  let μ := recoveredMass a ha s c hc
  let (v : ℝ≥0∞) (b : ExactSLEGenerator.Driver) : IsFiniteMeasureOnCompacts (μ v b) := (hμ v b).1
  let (v : ℝ≥0∞) (b : ExactSLEGenerator.Driver) : (μ v b).Regular := (hμ v b).2
  refine ⟨s,c,hc,hs,hsum,hμ,hzero,hmeas,hprog,hmom,hcompact,hL1,hmean,hH,?_⟩
  filter_upwards [hconv] with b hb
  rcases hb with ⟨horder,hvague,hfuture,hatom⟩
  have hpast (i : ℕ) (v : ℝ≥0) (hi : t i=v) : μ (t i) b {z : UpperPlane | alive a b.1 v z.1}=0 := by
    apply actual_limit_past_hull_support a ha s c hs b v (μ (t i) b)
    intro f
    have he := hvague i f
    simpa only [hi] using he
  refine ⟨horder,hvague,hatom,hpast,hfuture,?_⟩
  intro i j v hi hj
  have hdead := hfuture i j (hi ▸ ENNReal.coe_ne_top) hj
  have hreal : (t i).toNNReal=v := by rw [hi,ENNReal.toNNReal_coe]
  rw [hreal] at hdead
  have hU : MeasurableSet {z : UpperPlane | alive a b.1 v z.1} := by
    exact ((isOpen_alive b.1.continuous v).preimage
      (continuous_subtype_val : Continuous (Subtype.val : UpperPlane → ℂ))).measurableSet
  apply restriction_of_complementary_support (μ (t i) b) (μ (t j) b)
    (horder i j (by rw [hj]; exact le_top)) {z : UpperPlane | ¬alive a b.1 v z.1}
    hU.compl _ hdead
  simpa only [show {z : UpperPlane | ¬alive a b.1 v z.1} =
    ({z : UpperPlane | alive a b.1 v z.1})ᶜ from rfl, compl_compl] using hpast i v hi

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.TraceMassIntegration
open FlowIdentification ExactSLEGenerator ExactSLEMain ExactSLEGreen

lemma a_gt_quarter {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8) :
    1/4<Target.a κ := by
  unfold Target.a
  apply (lt_div_iff₀ hκ).mpr
  linarith

 

lemma past_trace_subset_dead {κ : ℝ} (hκ : 0<κ) (b : TDriver)
    (hlim : ∀ v : ℝ, 0≤v → Tendsto (fun y : ℝ => LiteralTrace.inverseFlow κ b (κ*v)
      (LiteralTrace.driverValue b (κ*v)+y*Complex.I)) (𝓝[>] 0)
        (𝓝 (LiteralTrace.trace κ b v))) {t : ℝ} (ht : 0≤t) :
    (Target.trace κ b) '' Icc 0 t ⊆
      {z | ¬alive (Target.a κ) (driverHomeomorph b).1 (κ*t).toNNReal z} := by
  rintro z ⟨v,hv,rfl⟩ hz
  have hs : LiteralTrace.Surviving κ b (LiteralTrace.trace κ b v) (κ*t) := by
    simpa only [surviving_eq,trace_eq_literal,
      Real.coe_toNNReal _ (mul_nonneg hκ.le ht)] using
        (surviving_iff_alive κ b (Target.trace κ b v) (κ*t).toNNReal).mpr hz
  exact LiteralTrace.radial_limit_not_surviving hκ (mul_nonneg hκ.le hv.1) b (hlim v hv.1)
    (LiteralTrace.surviving_of_le (mul_nonneg hκ.le hv.1)
      (mul_le_mul_of_nonneg_left hv.2 hκ.le) hs)

 

theorem actual_mass_remaining_avoids_past {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure TDriver) (hW : Target.IsWiener W) (t : ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
      (hc : ∀ k j, j∈s k → 0≤c k j),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k, ∑ j∈s k, c k j=1) ∧
      let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
      (∀ v b, IsFiniteMeasureOnCompacts (μ v b) ∧ (μ v b).Regular) ∧
      (∀ b, μ 0 b=0) ∧ (∀ v, Measurable (μ v)) ∧
      IsProgressive rawFiltration (fun v : ℝ≥0 => μ v) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)) (m : ℕ),
        MemLp (fun b => ∫z,f z∂μ (t i) b) (m : ℝ≥0∞) (W.map driverHomeomorph)) ∧
      (∀ i (K : Set UpperPlane), IsCompact K → ∀ m : ℕ,
        MemLp (fun b => (μ (t i) b K).toReal) (m : ℝ≥0∞) (W.map driverHomeomorph)) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)),
        Tendsto (fun k => eLpNorm (fun b =>
          (∑ j∈s k, c k j * ∫z,f z∂actualUpperMass (Target.a κ)
              (Real.exp (-2*(Target.a κ)*(j+1))) (t i) b) - ∫z,f z∂μ (t i) b)
              1 (W.map driverHomeomorph)) atTop (𝓝 0)) ∧
      (∀ i, t i=∞ → μ (t i) ∘ₘ (W.map driverHomeomorph)=initialGreenMeasure (Target.a κ)) ∧
      (∀ i j (v : ℝ≥0), t i=v → t j=∞ →
        ∀ H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞,
        Measurable[(rawFiltration v).prod (inferInstance : MeasurableSpace UpperPlane)] H →
        (∫⁻b, ∫⁻z, H (b,z) ∂μ (t j) b ∂(W.map driverHomeomorph)) =
          (∫⁻b, ∫⁻z, H (b,z) ∂μ (t i) b ∂(W.map driverHomeomorph)) +
            ∫⁻b, ∫⁻z, H (b,z) * ENNReal.ofReal (survivingGreen (Target.a κ) v b z.1)
              ∂upperArea ∂(W.map driverHomeomorph)) ∧
      ∀ᵐ b ∂W,
        ContinuousOn (Target.trace κ b) (Ici 0) ∧
        (∀ i j, t i≤t j → μ (t i) (driverHomeomorph b)≤μ (t j) (driverHomeomorph b)) ∧
        (∀ i (f : C_c(UpperPlane,ℝ)),
          Tendsto (fun k => ∑ j∈s k, c k j *
            ∫z,f z∂actualUpperMass (Target.a κ) (Real.exp (-2*(Target.a κ)*(j+1)))
              (t i) (driverHomeomorph b)) atTop (𝓝 (∫z,f z∂μ (t i) (driverHomeomorph b)))) ∧
        (∀ i, NullSingletonClass (μ (t i) (driverHomeomorph b))) ∧
        (∀ i (v : ℝ≥0), t i=v →
          μ (t i) (driverHomeomorph b)
            {z : UpperPlane | alive (Target.a κ) (driverHomeomorph b).1 v z.1}=0) ∧
        (∀ i j, t i≠∞ → t j=∞ →
          (μ (t j) (driverHomeomorph b)-μ (t i) (driverHomeomorph b))
            {z : UpperPlane | ¬alive (Target.a κ) (driverHomeomorph b).1 (t i).toNNReal z.1}=0) ∧
        (∀ i j (v : ℝ≥0), t i=v → t j=∞ →
          μ (t i) (driverHomeomorph b) =
            (μ (t j) (driverHomeomorph b)).restrict
              {z : UpperPlane | ¬alive (Target.a κ) (driverHomeomorph b).1 v z.1}) ∧
        (∀ i j (v : ℝ≥0), t i=v → t j=∞ →
          (μ (t j) (driverHomeomorph b)-μ (t i) (driverHomeomorph b))
            {z : UpperPlane | z.1∈(Target.trace κ b) '' Icc 0 ((v:ℝ)/κ)}=0) := by
  have hBW := brownian_map_driver W hW
  have : IsProbabilityMeasure (W.map driverHomeomorph) := hBW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨s,c,hc,hs,hcs,hμ,hzero,hmeas,hprog,hmom,hcompact,hL1,hmean,hcond,hconv⟩ :=
    actual_raw_mass_hull_accounting (Target.a κ) (a_gt_quarter hκ hκ8)
      (W.map driverHomeomorph) hBW t
  refine ⟨s,c,hc,hs,hcs,hμ,hzero,hmeas,hprog,hmom,hcompact,hL1,hmean,hcond,?_⟩
  filter_upwards [ae_of_ae_map measurable_driverHomeomorph.aemeasurable hconv,
    LiteralTrace.trace_regular_all_times hκ hκ8 hW] with b hb htrace
  rcases hb with ⟨horder, hvague, hatom, hpast, hfuture, haccount⟩
  refine ⟨?_,horder,hvague,hatom,hpast,hfuture,haccount,?_⟩
  · simpa only [trace_eq_literal] using htrace.2.1
  · intro i j v hi hj
    have hint : t i ≠ ∞ := hi ▸ ENNReal.coe_ne_top
    have hf := hfuture i j hint hj
    have hreal : (t i).toNNReal = v := by rw [hi,ENNReal.toNNReal_coe]
    rw [hreal] at hf
    have hp := past_trace_subset_dead hκ b htrace.1 (t := (v:ℝ)/κ) (by positivity)
    have he : (κ*((v:ℝ)/κ)).toNNReal=v := by
      rw [mul_div_cancel₀ _ hκ.ne',Real.toNNReal_coe]
    rw [he] at hp
    exact measure_mono_null (fun z hz => hp hz) hf

end SLEExactGauge.TraceMassIntegration
end
end

end OAI
