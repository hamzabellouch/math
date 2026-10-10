import Mathlib
import OAI.Probability.SKFluctuations.InverseMomentIntegrability

namespace OAI

/-! Inverse Control Measure Calculus. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology ENNReal

 theorem control_measures_finite (μ : Measure ℝ) [IsFiniteMeasure μ]
    {ρ w : ℝ → ℝ} {C : ℝ}
    (hρ : Measurable ρ) (hw : Measurable w)
    (hρb : ∀ᵐ x ∂μ, ρ x ∈ Icc (0:ℝ) C)
    (hwb : ∀ᵐ x ∂μ, w x ∈ Icc (0:ℝ) 1) :
    IsFiniteMeasure (controlPlusMeasure μ ρ w) ∧ IsFiniteMeasure (controlMinusMeasure μ ρ w) := by
  have hi (v : ℝ → ℝ) (hv : Measurable v) (hvb : ∀ᵐ x ∂μ, v x ∈ Icc (0:ℝ) 1) :
      IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (ρ x*v x))) := by
    apply isFiniteMeasure_withDensity
    apply (lintegral_ofReal_ne_top_iff_integrable
      ((hρ.mul hv).aestronglyMeasurable) ?_).mpr
    · apply Integrable.of_bound ((hρ.mul hv).aestronglyMeasurable) C
      filter_upwards [hρb,hvb] with x hx hvx
      change |ρ x*v x| ≤ C
      rw [abs_of_nonneg (mul_nonneg hx.1 hvx.1)]
      exact (mul_le_mul_of_nonneg_left hvx.2 hx.1).trans (by simpa using hx.2)
    · filter_upwards [hρb,hvb] with x hx hvx
      exact mul_nonneg hx.1 hvx.1
  exact ⟨hi (fun x => 1-w x) (measurable_const.sub hw) (hwb.mono fun x hx => by
    constructor <;> linarith [hx.1,hx.2]), hi w hw hwb⟩

 theorem integral_controlPlus (μ : Measure ℝ) {ρ w : ℝ → ℝ}
    (hρ : Measurable ρ) (hw : Measurable w)
    (hρp : ∀ᵐ x ∂μ, 0 ≤ ρ x) (hwb : ∀ᵐ x ∂μ, w x ≤ 1) (f : ℝ → ℝ) :
    (∫ x, f x ∂controlPlusMeasure μ ρ w)=∫ x, (ρ x*(1-w x))*f x ∂μ := by
  unfold controlPlusMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x => ENNReal.ofReal (ρ x*(1-w x))) from
      (hρ.mul (measurable_const.sub hw)).ennreal_ofReal)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  filter_upwards [hρp,hwb] with x hxρ hxw
  rw [ENNReal.toReal_ofReal (mul_nonneg hxρ (sub_nonneg.mpr hxw)),smul_eq_mul]

 theorem integral_controlMinus (μ : Measure ℝ) {ρ w : ℝ → ℝ}
    (hρ : Measurable ρ) (hw : Measurable w)
    (hρp : ∀ᵐ x ∂μ, 0 ≤ ρ x) (hwb : ∀ᵐ x ∂μ, 0 ≤ w x) (f : ℝ → ℝ) :
    (∫ x, f x ∂controlMinusMeasure μ ρ w)=∫ x, (ρ x*w x)*f x ∂μ := by
  unfold controlMinusMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x => ENNReal.ofReal (ρ x*w x)) from (hρ.mul hw).ennreal_ofReal)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  filter_upwards [hρp,hwb] with x hxρ hxw
  rw [ENNReal.toReal_ofReal (mul_nonneg hxρ hxw),smul_eq_mul]

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology ENNReal

 theorem control_measures_nonzero {a b lo hi : ℝ} (hab : a ≤ b)
    {α k m ρ w : ℝ → ℝ} (hα : AbsolutelyContinuousOnInterval α a b)
    (hρ : Measurable ρ) (hw : Measurable w)
    (hρp : ∀ᵐ x, x ∈ Icc a b → 0<ρ x)
    (hwb : ∀ᵐ x, x ∈ Icc a b → w x ∈ Icc (0:ℝ) 1)
    (heq : ∀ᵐ x, x ∈ Icc a b → deriv α x=k x+w x*(m x-k x))
    (hk : ∀ᵐ x, x ∈ Icc a b → k x ≤ lo)
    (hm : ∀ᵐ x, x ∈ Icc a b → hi ≤ m x)
    (hlo : lo*(b-a)<α b-α a) (hhi : α b-α a<hi*(b-a)) :
    controlPlusMeasure (volume.restrict (Icc a b)) ρ w≠0 ∧
      controlMinusMeasure (volume.restrict (Icc a b)) ρ w≠0 := by
  constructor
  · intro hzero
    have hz : (fun x => ENNReal.ofReal (ρ x*(1-w x)))=ᵐ[volume.restrict (Icc a b)] 0 :=
      (withDensity_eq_zero_iff ((hρ.mul (measurable_const.sub hw)).ennreal_ofReal.aemeasurable)).mp hzero
    have hz' := (ae_restrict_iff' measurableSet_Icc).mp hz
    have hder : (fun _ : ℝ => hi) ≤ᵐ[volume.restrict (Icc a b)] deriv α := by
      apply (ae_restrict_iff' measurableSet_Icc).mpr
      filter_upwards [hz',hρp,hwb,heq,hm] with x hx hxp hxw hxe hxm hxi
      have hp := hxp hxi
      have hb := hxw hxi
      have hz₁ : ρ x*(1-w x) ≤ 0 := ENNReal.ofReal_eq_zero.mp (hx hxi)
      have hw₁ : w x=1 := by nlinarith [hb.1,hb.2]
      rw [hxe hxi,hw₁]
      linarith [hxm hxi]
    have hi₁ := intervalIntegral.integral_mono_ae_restrict hab
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => hi) volume a b)
      hα.intervalIntegrable_deriv hder
    rw [hα.integral_deriv_eq_sub,intervalIntegral.integral_const] at hi₁
    simp only [smul_eq_mul] at hi₁
    nlinarith
  · intro hzero
    have hz : (fun x => ENNReal.ofReal (ρ x*w x))=ᵐ[volume.restrict (Icc a b)] 0 :=
      (withDensity_eq_zero_iff ((hρ.mul hw).ennreal_ofReal.aemeasurable)).mp hzero
    have hz' := (ae_restrict_iff' measurableSet_Icc).mp hz
    have hder : deriv α ≤ᵐ[volume.restrict (Icc a b)] (fun _ : ℝ => lo) := by
      apply (ae_restrict_iff' measurableSet_Icc).mpr
      filter_upwards [hz',hρp,hwb,heq,hk] with x hx hxp hxw hxe hxk hxi
      have hp := hxp hxi
      have hb := hxw hxi
      have hz₁ : ρ x*w x ≤ 0 := ENNReal.ofReal_eq_zero.mp (hx hxi)
      have hw₁ : w x=0 := by nlinarith [hb.1,hb.2]
      rw [hxe hxi,hw₁]
      simpa using hxk hxi
    have hi₁ := intervalIntegral.integral_mono_ae_restrict hab hα.intervalIntegrable_deriv
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => lo) volume a b) hder
    rw [hα.integral_deriv_eq_sub,intervalIntegral.integral_const] at hi₁
    simp only [smul_eq_mul] at hi₁
    nlinarith

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology

 theorem countable_nonzero_deriv_level (f : ℝ → ℝ) (c : ℝ) :
    {x | f x=c ∧ deriv f x≠0}.Countable := by
  apply (countable_setOfPred_isolated_right_within (s := {x | f x=c})).mono
  intro x hx
  refine ⟨hx.1,?_⟩
  have hd : DifferentiableAt ℝ f x := by
    by_contra h
    exact hx.2 (deriv_zero_of_not_differentiableAt h)
  have he : ∀ᶠ y in 𝓝[{y | f y=c} ∩ Ioi x] x, f y≠c :=
    (hd.hasDerivAt.eventually_ne hx.2).filter_mono (nhdsWithin_mono x (by
      intro y hy
      exact ne_of_gt hy.2))
  have hm : ∀ᶠ y in 𝓝[{y | f y=c} ∩ Ioi x] x, f y=c :=
    Filter.mem_of_superset self_mem_nhdsWithin (fun y hy => hy.1)
  apply Filter.empty_mem_iff_bot.mp
  filter_upwards [he,hm] with y hy₁ hy₂
  exact hy₁ hy₂

 theorem ae_deriv_zero_on_level (f : ℝ → ℝ) (c : ℝ) :
    ∀ᵐ x, f x=c → deriv f x=0 := by
  filter_upwards [(countable_nonzero_deriv_level f c).ae_notMem volume] with x hx hxc
  by_contra h
  exact hx ⟨hxc,h⟩

 theorem ae_contact_gradient_zero {a b : ℝ} {H J G : ℝ → ℝ}
    (hJ : ∀ x ∈ Icc a b, 0<J x)
    (hH : ∀ᵐ x, x ∈ Icc a b → HasDerivAt H (J x*G x) x) :
    ∀ᵐ x, x ∈ Icc a b → H x=0 → G x=0 := by
  filter_upwards [hH,ae_deriv_zero_on_level H 0] with x hx hz hxi hzero
  have he := hz hzero
  rw [(hx hxi).deriv] at he
  exact (mul_eq_zero.mp he).resolve_left (hJ x hxi).ne'

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology ENNReal

 def controlPrimitiveExtension {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
   ∫ y in a..(projIcc a b hab x).val, f y

 theorem controlPrimitiveExtension_on {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    {x : ℝ} (hx : x ∈ Icc a b) :
    controlPrimitiveExtension hab f x=∫ y in a..x, f y := by
  simp only [controlPrimitiveExtension,projIcc_of_mem hab hx]

 theorem controlPrimitiveExtension_continuous {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) : Continuous (controlPrimitiveExtension hab f) := by
  have hp : ContinuousOn (fun x => ∫ y in a..x, f y) (Icc a b) := by
    simpa only [uIcc_of_le hab] using (hf.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
  exact hp.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun x => (projIcc a b hab x).property)

 theorem controlPrimitiveExtension_integrable {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (controlPrimitiveExtension hab f) μ := by
  have hp : ContinuousOn (fun x => ∫ y in a..x, f y) (Icc a b) := by
    simpa only [uIcc_of_le hab] using (hf.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hp
  exact Integrable.of_bound (controlPrimitiveExtension_continuous hab hf).measurable.aestronglyMeasurable C
    (Eventually.of_forall fun x => hC _ (projIcc a b hab x).property)

 theorem control_gradient_potential {a b lo hi C : ℝ} (hab : a ≤ b)
    {α k m ρ w J G : ℝ → ℝ}
    (hα : AbsolutelyContinuousOnInterval α a b)
    (hρ : Measurable ρ) (hw : Measurable w)
    (hρp : ∀ᵐ x, x ∈ Icc a b → 0<ρ x)
    (hρb : ∀ᵐ x, x ∈ Icc a b → ρ x ≤ C)
    (hwb : ∀ᵐ x, x ∈ Icc a b → w x ∈ Icc (0:ℝ) 1)
    (heq : ∀ᵐ x, x ∈ Icc a b → deriv α x=k x+w x*(m x-k x))
    (hk : ∀ᵐ x, x ∈ Icc a b → k x ≤ lo)
    (hm : ∀ᵐ x, x ∈ Icc a b → hi ≤ m x)
    (hlo : lo*(b-a)<α b-α a) (hhi : α b-α a<hi*(b-a))
    (hJ : ∀ x ∈ Icc a b, 0<J x)
    (hGJ : IntervalIntegrable (fun x => J x*G x) volume a b)
    (hvar : ∀ p q : ℝ → ℝ, Measurable p → Measurable q →
      (∃ D : ℝ, ∀ x, p x ∈ Icc (0:ℝ) D ∧ q x ∈ Icc (0:ℝ) D) →
      (∫ x, p x ∂controlPlusMeasure (volume.restrict (Icc a b)) ρ w)=
        (∫ x, q x ∂controlMinusMeasure (volume.restrict (Icc a b)) ρ w) →
      (∫ x, controlPrimitiveExtension hab (fun y => J y*G y) x*q x
        ∂controlMinusMeasure (volume.restrict (Icc a b)) ρ w) ≤
      ∫ x, controlPrimitiveExtension hab (fun y => J y*G y) x*p x
        ∂controlPlusMeasure (volume.restrict (Icc a b)) ρ w) :
    ∃ H : ℝ → ℝ, AbsolutelyContinuousOnInterval H a b ∧
      (∀ᵐ x, x ∈ Icc a b → HasDerivAt H (J x*G x) x) ∧
      (∀ᵐ x, x ∈ Icc a b → (H x<0 → deriv α x=m x) ∧ (0<H x → deriv α x=k x)) ∧
      (∀ᵐ x, x ∈ Icc a b → H x=0 → G x=0) := by
  let μ := volume.restrict (Icc a b)
  have hρp' : ∀ᵐ x ∂μ, 0<ρ x := (ae_restrict_iff' measurableSet_Icc).mpr hρp
  have hwb' : ∀ᵐ x ∂μ, w x ∈ Icc (0:ℝ) 1 := (ae_restrict_iff' measurableSet_Icc).mpr hwb
  have hf := control_measures_finite μ hρ hw
    ((ae_restrict_iff' measurableSet_Icc).mpr (by
      filter_upwards [hρp,hρb] with x hp hb hx
      exact ⟨(hp hx).le,hb hx⟩)) hwb'
  let : IsFiniteMeasure (controlPlusMeasure μ ρ w) := hf.1
  let : IsFiniteMeasure (controlMinusMeasure μ ρ w) := hf.2
  have hn := control_measures_nonzero hab hα hρ hw hρp hwb heq hk hm hlo hhi
  obtain ⟨c,hc⟩ := control_bang_bang μ ρ w _ hρ hw hρp' hwb' hn.1 hn.2
    (controlPrimitiveExtension_continuous hab hGJ)
    (controlPrimitiveExtension_integrable hab hGJ _) (controlPrimitiveExtension_integrable hab hGJ _) hvar
  let H := fun x => (∫ y in a..x, J y*G y)-c
  have hHD : ∀ᵐ x, x ∈ Icc a b → HasDerivAt H (J x*G x) x := by
    have hd := hGJ.ae_hasDerivAt_integral
    simp only [uIcc_of_le hab] at hd
    filter_upwards [hd] with x hx hxi
    simpa only [H] using (hx hxi a ⟨le_rfl,hab⟩).sub_const c
  refine ⟨H,(hGJ.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).sub
    ((LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval),hHD,?_,ae_contact_gradient_zero hJ hHD⟩
  have hc' := (ae_restrict_iff' measurableSet_Icc).mp hc
  filter_upwards [hc',heq] with x hx he hxi
  rw [controlPrimitiveExtension_on hab _ hxi] at hx
  constructor
  · intro hneg
    rw [he hxi,(hx hxi).1 hneg]
    ring
  · intro hpos
    rw [he hxi,(hx hxi).2 hpos]
    ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 def controlFactorExtension {a b : ℝ} (hab : a ≤ b) (A : ℝ → ℝ) (r : ℝ) : ℝ :=
   Real.exp (controlPrimitiveExtension hab A r)

 theorem controlFactorExtension_pos {a b : ℝ} (hab : a ≤ b) (A : ℝ → ℝ) (r : ℝ) :
    0<controlFactorExtension hab A r := Real.exp_pos _

 theorem controlFactorExtension_on {a b : ℝ} (hab : a ≤ b) (A : ℝ → ℝ)
    {r : ℝ} (hr : r ∈ Icc a b) :
    controlFactorExtension hab A r=inverseControlFactor a A r := by
  simp only [controlFactorExtension,controlPrimitiveExtension_on hab A hr,inverseControlFactor]

 theorem controlFactorExtension_continuous {a b : ℝ} (hab : a ≤ b) {A : ℝ → ℝ}
    (hA : IntervalIntegrable A volume a b) : Continuous (controlFactorExtension hab A) :=
  Real.continuous_exp.comp (controlPrimitiveExtension_continuous hab hA)

 theorem control_density_bounds {a b gap : ℝ} (hab : a ≤ b) {m k A : ℝ → ℝ}
    (hm : ContinuousOn m (Icc a b)) (hk : ContinuousOn k (Icc a b))
    (hA : IntervalIntegrable A volume a b) (hg : 0<gap)
    (hgap : ∀ r ∈ Icc a b, gap ≤ m r-k r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc a b,
      (m r-k r)/controlFactorExtension hab A r ∈ Ioc (0:ℝ) C := by
  have hc : ContinuousOn (fun r => (m r-k r)/controlFactorExtension hab A r) (Icc a b) :=
    (hm.sub hk).div (controlFactorExtension_continuous hab hA).continuousOn
      (fun r _ => (controlFactorExtension_pos hab A r).ne')
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨C,(norm_nonneg _).trans (hC a ⟨le_rfl,hab⟩),?_⟩
  intro r hr
  have hp := div_pos (hg.trans_le (hgap r hr)) (controlFactorExtension_pos hab A r)
  exact ⟨hp,by simpa only [Real.norm_eq_abs,abs_of_pos hp] using hC r hr⟩

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology ENNReal

 theorem control_cost_identity (μ : Measure ℝ) [IsFiniteMeasure μ]
    {ρ w Q p q : ℝ → ℝ} {R K A : ℝ}
    (hρ : Measurable ρ) (hw : Measurable w) (hQ : Measurable Q)
    (hp : Measurable p) (hq : Measurable q)
    (hρb : ∀ᵐ x ∂μ, ρ x ∈ Icc (0:ℝ) R)
    (hwb : ∀ᵐ x ∂μ, w x ∈ Icc (0:ℝ) 1)
    (hQb : ∀ᵐ x ∂μ, |Q x| ≤ K)
    (hpq : ∀ x, p x ∈ Icc (0:ℝ) A ∧ q x ∈ Icc (0:ℝ) A) :
    (∫ x, Q x*ρ x*((1-w x)*p x-w x*q x) ∂μ)=
      (∫ x, Q x*p x ∂controlPlusMeasure μ ρ w)-
        ∫ x, Q x*q x ∂controlMinusMeasure μ ρ w := by
  have hA : 0 ≤ A := (hpq 0).1.1.trans (hpq 0).1.2
  have hi (v f : ℝ → ℝ) (hv : Measurable v) (hf : Measurable f)
      (hvb : ∀ᵐ x ∂μ, v x ∈ Icc (0:ℝ) 1)
      (hfb : ∀ x, f x ∈ Icc (0:ℝ) A) :
      Integrable (fun x => (ρ x*v x)*(Q x*f x)) μ := by
    apply Integrable.of_bound (((hρ.mul hv).mul (hQ.mul hf)).aestronglyMeasurable) (R*K*A)
    filter_upwards [hρb,hvb,hQb] with x hr hvx hqx
    have hR : 0 ≤ R := hr.1.trans hr.2
    have hK : 0 ≤ K := (abs_nonneg _).trans hqx
    change |ρ x*v x*(Q x*f x)| ≤ _
    rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg hr.1,abs_of_nonneg hvx.1,
      abs_of_nonneg (hfb x).1]
    calc
      ρ x*v x*(|Q x| * f x) ≤ R*(K*A) := by
        apply mul_le_mul _ (mul_le_mul hqx (hfb x).2 (hfb x).1 hK) (mul_nonneg (abs_nonneg _) (hfb x).1) hR
        exact (mul_le_mul_of_nonneg_left hvx.2 hr.1).trans (by simpa using hr.2)
      _ = R*K*A := by ring
  have hp' := hi (fun x => 1-w x) p (measurable_const.sub hw) hp
    (hwb.mono fun x hx => by constructor <;> linarith [hx.1,hx.2]) (fun x => (hpq x).1)
  have hq' := hi w q hw hq hwb (fun x => (hpq x).2)
  rw [integral_controlPlus μ hρ hw (hρb.mono fun _ h => h.1) (hwb.mono fun _ h => h.2),
    integral_controlMinus μ hρ hw (hρb.mono fun _ h => h.1) (hwb.mono fun _ h => h.1),
    ← integral_sub hp' hq']
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem integral_primitive_product {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    (∫ x in a..b, (∫ y in a..x, f y)*g x)=
      (∫ x in a..b, f x)*(∫ x in a..b, g x)-
        (∫ x in a..b, f x*(∫ y in a..x, g y)) := by
  have ha : a ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact ⟨le_rfl,hab⟩
  have hfa := hf.absolutelyContinuousOnInterval_intervalIntegral ha
  have hga := hg.absolutelyContinuousOnInterval_intervalIntegral ha
  have hfd := hf.ae_hasDerivAt_integral
  have hgd := hg.ae_hasDerivAt_integral
  have he₁ : (∫ x in a..b, (∫ y in a..x, f y)*g x)=
      ∫ x in a..b, (∫ y in a..x, f y)*deriv (fun z => ∫ y in a..z, g y) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hgd] with x hx hxi
    rw [(hx (uIoc_subset_uIcc hxi) a ha).deriv]
  have he₂ : (∫ x in a..b, deriv (fun z => ∫ y in a..z, f y) x*(∫ y in a..x, g y))=
      ∫ x in a..b, f x*(∫ y in a..x, g y) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hfd] with x hx hxi
    rw [(hx (uIoc_subset_uIcc hxi) a ha).deriv]
  rw [he₁,hfa.integral_mul_deriv_eq_deriv_mul hga,he₂]
  simp

 theorem inverse_control_cost {a b : ℝ} (hab : a ≤ b) {A F G : ℝ → ℝ}
    (hGF : IntervalIntegrable (fun x => G x*inverseControlFactor a A x) volume a b)
    (hFJ : IntervalIntegrable (fun x => F x/inverseControlFactor a A x) volume a b)
    (hendpoint : (∫ x in a..b, F x/inverseControlFactor a A x)=0) :
    -(∫ x in a..b, G x*inverseControlTangent a A F x)=
      ∫ x in a..b, (∫ y in a..x, G y*inverseControlFactor a A y)*
        (F x/inverseControlFactor a A x) := by
  rw [integral_primitive_product hab hGF hFJ,hendpoint,mul_zero,zero_sub]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [inverseControlTangent,inverseControlFactor,Real.exp_neg,div_eq_mul_inv]
  ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem control_first_variation_to_potential {r₀ u₀ gap U L lo hi : ℝ}
    {α k M M' w G : ℝ → ℝ} (hr : r₀ ≤ 1) {C : ℝ≥0}
    (hα : LipschitzOnWith C α (Icc r₀ 1)) (hα₀ : α r₀=u₀) (hα₁ : α 1=1)
    (hαm : Measurable α) (hkm : Measurable k) (hMc : Continuous M)
    (hM'm : Measurable M') (hkc : ContinuousOn k (Icc r₀ 1)) (hw : Measurable w)
    (hconv : ∀ u v, M u+M' u*(v-u) ≤ M v)
    (hg : 0<gap) (hU : 0 ≤ U) (hL : 0 ≤ L)
    (heq : ∀ᵐ r, r ∈ Icc r₀ 1 → deriv α r=k r+w r*(M (α r)-k r))
    (hbd : ∀ r ∈ Icc r₀ 1, w r ∈ Icc (0:ℝ) 1 ∧
      gap ≤ M (α r)-k r ∧ M (α r)-k r ≤ U ∧ |M' (α r)| ≤ L)
    (hklo : ∀ r ∈ Icc r₀ 1, k r ≤ lo) (hmhi : ∀ r ∈ Icc r₀ 1, hi ≤ M (α r))
    (hlo : lo*(1-r₀)<1-u₀) (hhi : 1-u₀<hi*(1-r₀))
    (hGi : IntervalIntegrable G volume r₀ 1)
    (hfirst : ∀ (ψ : ℝ → ℝ) (D : ℝ≥0) (B T : ℝ), 0<T → 0 ≤ B →
      LipschitzOnWith D ψ (Icc r₀ 1) → (∀ r ∈ Icc r₀ 1, |ψ r| ≤ B) →
      (∀ t ∈ Icc (0:ℝ) T, sourceInverseConstraints r₀ u₀ k M (fun r => α r+t*ψ r)) →
      0 ≤ -(∫ r in Icc r₀ 1, G r*ψ r)) :
    ∃ H : ℝ → ℝ, AbsolutelyContinuousOnInterval H r₀ 1 ∧
      (∀ᵐ r, r ∈ Icc r₀ 1 → HasDerivAt H
        (inverseControlFactor r₀ (fun x => w x*M' (α x)) r*G r) r) ∧
      (∀ᵐ r, r ∈ Icc r₀ 1 →
        (H r<0 → deriv α r=M (α r)) ∧ (0<H r → deriv α r=k r)) ∧
      (∀ᵐ r, r ∈ Icc r₀ 1 → H r=0 → G r=0) := by
  let a := fun r => w r*M' (α r)
  have ham : Measurable a := hw.mul (hM'm.comp hαm)
  have hab : ∀ᵐ r, r ∈ Icc r₀ 1 → |a r| ≤ L := Eventually.of_forall fun r hr' => by
    dsimp only [a]
    rw [abs_mul,abs_of_nonneg (hbd r hr').1.1]
    exact (mul_le_mul_of_nonneg_left (hbd r hr').2.2.2 (hbd r hr').1.1).trans
      (by nlinarith [(hbd r hr').1.2])
  have hai := bounded_measurable_intervalIntegrable hr ham hab
  let J := controlFactorExtension hr a
  have hJc : Continuous J := controlFactorExtension_continuous hr hai
  have hJp : ∀ r, 0<J r := controlFactorExtension_pos hr a
  let ρ := fun r => (M (α r)-k r)/J r
  have hρm : Measurable ρ := ((hMc.measurable.comp hαm).sub hkm).div hJc.measurable
  obtain ⟨R,hR,hρ⟩ := control_density_bounds hr (hMc.comp_continuousOn hα.continuousOn) hkc hai hg
    (fun r hr' => (hbd r hr').2.1)
  have hρp : ∀ᵐ r, r ∈ Icc r₀ 1 → 0<ρ r := Eventually.of_forall fun r hr' => (hρ r hr').1
  have hρb : ∀ᵐ r, r ∈ Icc r₀ 1 → ρ r ≤ R := Eventually.of_forall fun r hr' => (hρ r hr').2
  have hwb : ∀ᵐ r, r ∈ Icc r₀ 1 → w r ∈ Icc (0:ℝ) 1 :=
    Eventually.of_forall fun r hr' => (hbd r hr').1
  have hGJ : IntervalIntegrable (fun r => J r*G r) volume r₀ 1 :=
    hGi.continuousOn_mul hJc.continuousOn
  have hac : AbsolutelyContinuousOnInterval α r₀ 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
    simpa only [uIcc_of_le hr] using hα
  obtain ⟨H,hH,hHd,hHsign,hHz⟩ := control_gradient_potential hr hac hρm hw hρp hρb hwb heq
    (Eventually.of_forall hklo) (Eventually.of_forall hmhi)
    (by simpa only [hα₀,hα₁] using hlo) (by simpa only [hα₀,hα₁] using hhi)
    (fun r _ => hJp r) hGJ (by
      intro p q hp hq hpq hend
      obtain ⟨A,hpq⟩ := hpq
      have hA : 0 ≤ A := (hpq 0).1.1.trans (hpq 0).1.2
      let μ := volume.restrict (Icc r₀ 1)
      have hρμ : ∀ᵐ r ∂μ, ρ r ∈ Icc (0:ℝ) R := (ae_restrict_iff' measurableSet_Icc).mpr
        (Eventually.of_forall fun r hr' => ⟨(hρ r hr').1.le,(hρ r hr').2⟩)
      have hwμ : ∀ᵐ r ∂μ, w r ∈ Icc (0:ℝ) 1 := (ae_restrict_iff' measurableSet_Icc).mpr hwb
      let f := fun r => (M (α r)-k r)*((1-w r)*p r-w r*q r)
      have heqf {r : ℝ} (hri : r ∈ Icc r₀ 1) :
          f r/inverseControlFactor r₀ a r=ρ r*((1-w r)*p r-w r*q r) := by
        rw [show ρ r=(M (α r)-k r)/J r from rfl,
          show J r=inverseControlFactor r₀ a r from controlFactorExtension_on hr a hri]
        dsimp only [f]; ring
      have hend' : (∫ r in r₀..1, f r/inverseControlFactor r₀ a r)=0 := by
        rw [intervalIntegral.integral_of_le hr,← integral_Icc_eq_integral_Ioc]
        have he : (∫ r in Icc r₀ 1, f r/inverseControlFactor r₀ a r)=
            ∫ r in Icc r₀ 1, (1:ℝ)*ρ r*((1-w r)*p r-w r*q r) := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro r hri; simpa only [one_mul] using heqf hri
        rw [he,control_cost_identity μ hρm hw measurable_const hp hq hρμ hwμ
          (Eventually.of_forall fun _ => by norm_num : ∀ᵐ r ∂μ, |(1:ℝ)| ≤ 1) hpq]
        simpa only [one_mul,sub_self] using sub_eq_zero.mpr hend
      obtain ⟨T,B,D,hT,hB,hψ,hψb,hfeas⟩ := bounded_control_competitors hr hα hα₀ hα₁
        hαm hkm hMc.measurable hM'm hw hp hq hconv hg hU hL hA heq
        (fun r hr' => ⟨(hbd r hr').1,(hbd r hr').2.1,(hbd r hr').2.2.1,
          (hbd r hr').2.2.2,(hpq r).1,(hpq r).2⟩) hend'
      let ψ := inverseControlTangent r₀ a f
      have hcost := hfirst ψ D B T hT hB hψ hψb hfeas
      have hGF : IntervalIntegrable (fun r => G r*inverseControlFactor r₀ a r) volume r₀ 1 := by
        apply hGJ.congr_uIoo
        intro r hri
        have hri' : r ∈ Icc r₀ 1 := uIoo_subset_uIcc_self hri |> (by simpa only [uIcc_of_le hr] using ·)
        change J r*G r=G r*inverseControlFactor r₀ a r
        rw [← controlFactorExtension_on hr a hri']
        exact mul_comm _ _
      have hFJ : IntervalIntegrable (fun r => f r/inverseControlFactor r₀ a r) volume r₀ 1 := by
        have hh := bounded_measurable_intervalIntegrable hr
          (hρm.mul (((measurable_const.sub hw).mul hp).sub (hw.mul hq)))
          (Eventually.of_forall fun r (hri : r ∈ Icc r₀ 1) => show
            |ρ r*((1-w r)*p r-w r*q r)| ≤ R*A by
              rw [abs_mul,abs_of_pos (show 0<ρ r from (hρ r hri).1)]
              exact mul_le_mul (hρ r hri).2
                (control_difference_bound (hbd r hri).1 (hpq r).1 (hpq r).2) (abs_nonneg _) hR)
        apply hh.congr_uIoo
        intro r hri
        apply (heqf ?_).symm
        simpa only [uIcc_of_le hr] using uIoo_subset_uIcc_self hri
      have hibp := inverse_control_cost hr hGF hFJ hend'
      rw [intervalIntegral.integral_of_le hr,← integral_Icc_eq_integral_Ioc] at hibp
      rw [hibp] at hcost
      let Q := controlPrimitiveExtension hr (fun r => J r*G r)
      have hQc : Continuous Q := controlPrimitiveExtension_continuous hr hGJ
      obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hQc.continuousOn
      have hQμ : ∀ᵐ r ∂μ, |Q r| ≤ K := (ae_restrict_iff' measurableSet_Icc).mpr
        (Eventually.of_forall fun r hri => by simpa only [Real.norm_eq_abs] using hK r hri)
      have hQon {r : ℝ} (hri : r ∈ Icc r₀ 1) :
          Q r=∫ y in r₀..r, G y*inverseControlFactor r₀ a y := by
        dsimp only [Q]
        rw [controlPrimitiveExtension_on hr _ hri]
        apply intervalIntegral.integral_congr
        intro y hy
        have hy' : y ∈ Icc r₀ 1 := by
          rw [uIcc_of_le hri.1] at hy
          exact ⟨hy.1,hy.2.trans hri.2⟩
        change J y*G y=G y*inverseControlFactor r₀ a y
        rw [show J y=inverseControlFactor r₀ a y from controlFactorExtension_on hr a hy']
        ring
      have hecost : (∫ r in r₀..1, (∫ y in r₀..r, G y*inverseControlFactor r₀ a y)*
          (f r/inverseControlFactor r₀ a r))=
          (∫ r in Icc r₀ 1, Q r*ρ r*((1-w r)*p r-w r*q r)) := by
        rw [intervalIntegral.integral_of_le hr,← integral_Icc_eq_integral_Ioc]
        apply setIntegral_congr_fun measurableSet_Icc
        intro r hri
        change (∫ y in r₀..r, G y*inverseControlFactor r₀ a y)*
          (f r/inverseControlFactor r₀ a r)=Q r*ρ r*((1-w r)*p r-w r*q r)
        rw [← hQon hri,heqf hri]
        ring
      rw [hecost,control_cost_identity μ hρm hw hQc.measurable hp hq hρμ hwμ hQμ hpq] at hcost
      exact sub_nonneg.mp hcost)
  refine ⟨H,hH,?_,hHsign,hHz⟩
  filter_upwards [hHd] with r hd hri
  rw [← controlFactorExtension_on hr a hri]
  exact hd hri

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 def inverseControlWeight (α k M : ℝ → ℝ) (r : ℝ) : ℝ :=
   max 0 (min 1 ((deriv α r-k r)/(M (α r)-k r)))

 theorem inverseControlWeight_mem (α k M : ℝ → ℝ) (r : ℝ) :
    inverseControlWeight α k M r ∈ Icc (0:ℝ) 1 := by
  unfold inverseControlWeight
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

 theorem inverseControlWeight_measurable {α k M : ℝ → ℝ}
    (hα : Measurable α) (hk : Measurable k) (hM : Measurable M) :
    Measurable (inverseControlWeight α k M) := by
  unfold inverseControlWeight
  exact measurable_const.max (measurable_const.min
    (((measurable_deriv α).sub hk).div ((hM.comp hα).sub hk)))

 theorem inverseControlWeight_equation {α k M : ℝ → ℝ} {r : ℝ}
    (hk : k r ≤ deriv α r) (hM : deriv α r ≤ M (α r)) (hm : k r<M (α r)) :
    deriv α r=k r+inverseControlWeight α k M r*(M (α r)-k r) := by
  have hp : 0<M (α r)-k r := sub_pos.mpr hm
  have hq : (deriv α r-k r)/(M (α r)-k r) ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hk) hp.le,(div_le_one hp).mpr (sub_le_sub_right hM _)⟩
  unfold inverseControlWeight
  rw [min_eq_right hq.2,max_eq_right hq.1,div_mul_cancel₀ _ hp.ne']
  ring

 theorem inverseControlWeight_ae_equation {r₀ u₀ : ℝ} {α k M : ℝ → ℝ}
    (hα : sourceInverseConstraints r₀ u₀ k M α)
    (hm : ∀ r ∈ Icc r₀ 1, k r<M (α r)) :
    ∀ᵐ r, r ∈ Icc r₀ 1 →
      deriv α r=k r+inverseControlWeight α k M r*(M (α r)-k r) := by
  obtain ⟨C,hC,hae⟩ := hα.2.2
  filter_upwards [hae] with r hr hri
  exact inverseControlWeight_equation (hr hri).1 (hr hri).2 (hm r hri)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

 theorem source_minimum_potential {r₀ u₀ c gap U L lo hi : ℝ} {k M M' g : ℝ → ℝ}
    (hr : r₀ ≤ 1) (hu : u₀ ∈ Icc (0:ℝ) 1) (hc : 0<c)
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ r ∈ Icc r₀ 1, c ≤ k r)
    (hkm : Measurable k) (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (hMc : Continuous M) (hM'm : Measurable M')
    (hconv : ∀ u v, M u+M' u*(v-u) ≤ M v)
    (hg0 : 0<gap) (hU : 0 ≤ U) (hL : 0 ≤ L)
    (α : inverseIntegralConstraints r₀ u₀ k M)
    (hbd : ∀ r ∈ Icc r₀ 1, gap ≤ M (α.val.val r)-k r ∧
      M (α.val.val r)-k r ≤ U ∧ |M' (α.val.val r)| ≤ L)
    (hklo : ∀ r ∈ Icc r₀ 1, k r ≤ lo)
    (hmhi : ∀ r ∈ Icc r₀ 1, hi ≤ M (α.val.val r))
    (hlo : lo*(1-r₀)<1-u₀) (hhi : 1-u₀<hi*(1-r₀))
    (hg : ContDiff ℝ 1 g) (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    (hb : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => b u-omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) u) (Icc (0:ℝ) 1))
    (hh : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => h u+omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
          (hg.continuous.mul continuous_id) β) u) (Icc (0:ℝ) 1))
    (hbn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ b 0-omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) 0)
    (hhn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ h 0+omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) β) 0)
    (hmin : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 α ≤
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 β) :
    let b' := fun u => (b u-omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) u).toNNReal
    let h' := fun u => (h u+omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) α) u).toNNReal
    let G := radiusComparisonGradient g α.val.val (orderedPathS n b' h') (orderedPathB n b' h')
    let w := inverseControlWeight α.val.val k M
    let J := inverseControlFactor r₀ (fun r => w r*M' (α.val.val r))
    ∃ H : ℝ → ℝ, AbsolutelyContinuousOnInterval H r₀ 1 ∧
      (∀ᵐ r, r ∈ Icc r₀ 1 → HasDerivAt H (J r*G r) r) ∧
      (∀ᵐ r, r ∈ Icc r₀ 1 →
        (H r<0 → deriv α.val.val r=M (α.val.val r)) ∧
        (0<H r → deriv α.val.val r=k r)) ∧
      (∀ᵐ r, r ∈ Icc r₀ 1 → H r=0 → G r=0) := by
  dsimp only
  let b' := fun u => (b u-omittedExtension hu.2
    (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) u).toNNReal
  let h' := fun u => (h u+omittedExtension hu.2
    (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
      (hg.continuous.mul continuous_id) α) u).toNNReal
  let w := inverseControlWeight α.val.val k M
  have hαm : Measurable α.val.val := α.val.property.2.measurable
  have hαd : sourceInverseConstraints r₀ u₀ k M α.val.val := by
    have hd : α.val ∈ inverseDifferentialConstraints r₀ u₀ k M := by
      rw [inverseDifferentialConstraints_eq r₀ u₀ hr k M hk hMc hm hM]
      exact α.property
    exact hd
  apply control_first_variation_to_potential hr (inverseIntegralConstraints_lipschitz hm hM α.property)
    α.property.1 α.property.2.1 hαm hkm hMc hM'm hk
    (inverseControlWeight_measurable hαm hkm hMc.measurable) hconv hg0 hU hL
    (inverseControlWeight_ae_equation hαd (fun r hri => by linarith [(hbd r hri).1]))
    (fun r hri => ⟨inverseControlWeight_mem _ _ _ _,hbd r hri⟩) hklo hmhi hlo hhi
  · apply source_radius_gradient_integrable hr hu hc hk hkc hm hM α hg n hn b' h'
    · exact fun u hu v hv huv => Real.toNNReal_mono ((hb α) hu hv huv)
    · exact fun u hu v hv huv => Real.toNNReal_mono ((hh α) hu hv huv)
  · intro ψ D B T hT hB hψ hψb hfeas
    exact source_minimum_first_variation hr hu hc hk hkc hm hM hMc α hfeas hT hB hψ hψb
      hg n hn b h hb hh hbn hhn hmin

end SKFluctuations

end

end OAI
