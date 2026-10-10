import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.RadialConditionalMixing

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator CenteredMoments

lemma radialLaw_normalize_integral (W : Measure GDriver)
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (w : UpperPlane) (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (f : GDriver→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻b,f (normalizeDriver w b)∂radialLaw W a w.1 (w.1.im*q))=
      ∫⁻b,f b∂radialLaw W a (fromDisk (pointAngle w).1 0)
        (Real.sin (pointAngle w).1*q) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi (pointAngle w).2.1 (pointAngle w).2.2
  have hz : 0<(fromDisk (pointAngle w).1 0).im := by simpa only [fromDisk_zero_im] using hs
  have he : (‖w.1‖:ℝ)*(Real.sin (pointAngle w).1*q)=w.1.im*q := by
    rw [sin_pointAngle]
    field_simp [(point_norm_pos w).ne']
  have hr : Real.sin (pointAngle w).1*q≤(fromDisk (pointAngle w).1 0).im := by
    rw [fromDisk_zero_im]
    exact mul_le_of_le_one_right hs.le hq1
  have hh := radialLaw_scale_integral W hW a ha (c:=‖w.1‖₊) (point_norm_pos w)
    _ hz _ (mul_pos hs hq) hr f hf
  simp only [coe_nnnorm] at hh
  rw [norm_mul_fromDisk_pointAngle,he] at hh
  exact hh

 
def finiteTestKernel (W : Measure GDriver) (a : ℝ) (l : ℕ)
    (f : Angle×GDriver→ℝ≥0∞) (θ : Angle) : ℝ≥0∞ :=
  ∫⁻b,f (θ,b)∂radialLaw W a (fromDisk θ.1 0) (Real.sin θ.1*Real.exp (-2*a*l))

lemma finiteTestKernel_eq (W : Measure GDriver) (a : ℝ) (ha : 1/4<a) (l : ℕ)
    (f : Angle×GDriver→ℝ≥0∞) (hf : Measurable f) (θ : Angle) :
    finiteTestKernel W a l f θ=
      ∫⁻b,ENNReal.ofReal (tiltWeight a θ.1 b.1 l)*f (θ,b)∂W := by
  have hm := (centeredWeight_measurable a ha l).ennreal_ofReal.comp
    ((measurable_const (a:=θ)).prodMk measurable_id)
  have he : (fun b : GDriver => ENNReal.ofReal (tiltWeight a θ.1 b.1 l))=
      radiusDensity a (fromDisk θ.1 0) (Real.sin θ.1*Real.exp (-2*a*l)) := by
    funext b
    rw [radiusDensity,tiltWeight_radialWeight a θ.1 ha θ.2.1 θ.2.2 b l]
  unfold finiteTestKernel radialLaw
  change (∫⁻b,f (θ,b)∂W.withDensity
    (radiusDensity a (fromDisk θ.1 0) (Real.sin θ.1*Real.exp (-2*a*l))))=_
  rw [←he]
  exact lintegral_withDensity_eq_lintegral_mul W hm
    (hf.comp (measurable_const.prodMk measurable_id))

lemma finiteTestKernel_measurable (W : Measure GDriver) [SFinite W]
    (a : ℝ) (ha : 1/4<a) (l : ℕ) (f : Angle×GDriver→ℝ≥0∞) (hf : Measurable f) :
    Measurable (finiteTestKernel W a l f) := by
  simp_rw [funext (finiteTestKernel_eq W a ha l f hf)]
  exact ((centeredWeight_measurable a ha l).ennreal_ofReal.mul hf).lintegral_prod_right'

lemma finiteTestKernel_mixed (W : Measure GDriver) [SFinite W]
    (a : ℝ) (ha : 1/4<a) (l : ℕ) (f : Angle×GDriver→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻θ,finiteTestKernel W a l f θ∂angleLaw a)=∫⁻p,f p∂finiteAngleLaw W a l :=
  (finiteAngleLaw_lintegral W a ha l f hf).symm

lemma pointAngle_radialPoint (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (σ : ℝ) (hσ : 0<σ) (hσz : σ≤z.im) (b : GDriver)
    (hb : radialTime a b.1 z σ≠∞) :
    pointAngle (radialPoint a z σ b)=Jacobi.finiteAngle a z σ b := by
  apply Subtype.ext
  change physicalTheta ((radialPoint a z σ b).1,0)=physicalTheta (radialState a b.1 z σ)
  rw [radialPoint_eq a ha z hz σ hσ hσz b hb,radialState,ite_eq_right hb]
  rfl

 
def normalizedTest (a : ℝ) (z : ℂ) (σ : ℝ) (f : Angle×GDriver→ℝ≥0∞)
    (b : GDriver) : ℝ≥0∞ :=
  f (pointAngle (radialPoint a z σ b),normalizeDriver (radialPoint a z σ b)
    (restartAt (fun c=>radialTime a c.1 z σ) b))

lemma normalizedTest_measurable (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (σ : ℝ) (hσ : 0<σ) (hσz : σ≤z.im) (f : Angle×GDriver→ℝ≥0∞) (hf : Measurable f) :
    Measurable (normalizedTest a z σ f) := by
  have hS := radialTime_stopping a (by linarith) z hz σ hσ hσz
  have hw := (radialPoint_raw_measurable a ha z hz σ hσ hσz).mono hS.measurableSpace_le le_rfl
  exact hf.comp ((pointAngle_measurable.comp hw).prodMk
    (continuous_normalizeDriver.measurable.comp (hw.prodMk (measurable_restartAt hS))))

 

theorem normalizedTest_conditional (W : Measure GDriver)
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im) (σ : ℝ) (hσ : 0<σ) (hσz : σ≤z.im)
    (l : ℕ) (A : Set GDriver)
    (hA : MeasurableSet[(radialTime_stopping a (by linarith) z hz σ hσ hσz).measurableSpace] A)
    (f : Angle×GDriver→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻b in A,normalizedTest a z σ f b∂radialLaw W a z (σ*Real.exp (-2*a*l)))=
      ∫⁻b in A,finiteTestKernel W a l f (Jacobi.finiteAngle a z σ b)∂radialLaw W a z σ := by
  let F : UpperPlane×GDriver→ℝ≥0∞ := fun p=>f (pointAngle p.1,normalizeDriver p.1 p.2)
  have hF : Measurable F := hf.comp ((pointAngle_measurable.comp measurable_fst).prodMk
    continuous_normalizeDriver.measurable)
  have hq1 : Real.exp (-2*a*l)≤1 := Real.exp_le_one_iff.mpr (by
    have ha0 : 0<a := by linarith
    have hl : (0:ℝ)≤l := Nat.cast_nonneg l
    nlinarith)
  have hq : 0<Real.exp (-2*a*l) := Real.exp_pos _
  have hρ := mul_pos hσ hq
  have hr := mul_le_of_le_one_right hσ.le hq1
  change (∫⁻b in A,F (radialPoint a z σ b,restartAt (fun c=>radialTime a c.1 z σ) b)
    ∂radialLaw W a z (σ*Real.exp (-2*a*l)))=_
  rw [radialLaw_restart W hW a ha z hz σ _ hρ hr hσz A hA F hF]
  have hrat : σ*Real.exp (-2*a*l)/σ=Real.exp (-2*a*l) := mul_div_cancel_left₀ _ hσ.ne'
  simp_rw [hrat]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (radial_hit_ae W a ha z hz σ hσ hσz)] with b hb
  change (∫⁻c,f (pointAngle (radialPoint a z σ b),normalizeDriver (radialPoint a z σ b) c)
    ∂radialLaw W a (radialPoint a z σ b).1 ((radialPoint a z σ b).1.im*Real.exp (-2*a*l)))=_
  rw [radialLaw_normalize_integral W hW a ha _ _ hq hq1
    (fun c=>f (pointAngle (radialPoint a z σ b),c))
    (hf.comp (measurable_const.prodMk measurable_id)),
    pointAngle_radialPoint a (by linarith) z hz σ hσ hσz b hb]
  rfl

 

theorem normalizedTest_conditional_bounds (W : Measure GDriver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (σ τ : ℝ) (hτ : 0<τ) (hτσ : τ≤σ) (hσ : σ≤z.im)
    (s : ℝ) (hs : Jacobi.mixingTime (4*a) ≤ s) (hgap : τ=σ*Real.exp (-2*a*s))
    (l : ℕ) (A : Set GDriver)
    (hA : MeasurableSet[(radialTime_stopping a (by linarith) z hz σ
      (hτ.trans_le hτσ) hσ).measurableSpace] A)
    (f : Angle×GDriver→ℝ≥0∞) (hf : Measurable f) :
    (1/2:ℝ≥0∞)*(∫⁻p,f p∂finiteAngleLaw W a l)*radialLaw W a z (τ*Real.exp (-2*a*l)) A ≤
      ∫⁻b in A,normalizedTest a z τ f b∂radialLaw W a z (τ*Real.exp (-2*a*l)) ∧
    (∫⁻b in A,normalizedTest a z τ f b∂radialLaw W a z (τ*Real.exp (-2*a*l))) ≤
      2*(∫⁻p,f p∂finiteAngleLaw W a l)*radialLaw W a z (τ*Real.exp (-2*a*l)) A := by
  have ha0 : 0<a := by linarith
  have hT := radialTime_stopping a ha0 z hz τ hτ (hτσ.trans hσ)
  have hS := radialTime_stopping a ha0 z hz σ (hτ.trans_le hτσ) hσ
  have hAτ : MeasurableSet[hT.measurableSpace] A :=
    (hS.measurableSpace_mono hT (radialTime_antitone a ha0 z hz τ σ hτ hτσ hσ)) _ hA
  have hq1 : Real.exp (-2*a*l)≤1 := Real.exp_le_one_iff.mpr (by
    have hl : (0:ℝ)≤l := Nat.cast_nonneg l
    nlinarith)
  have hr := mul_le_of_le_one_right hτ.le hq1
  rw [normalizedTest_conditional W hW a ha z hz τ hτ (hτσ.trans hσ) l A hAτ f hf,
    radialLaw_consistent_le W hW a ha z hz τ _ (mul_pos hτ (Real.exp_pos _)) hr
      (hτσ.trans hσ) A hAτ]
  have hh := finiteAngle_conditional_bounds W hW a ha z hz σ τ hτ hτσ hσ s hs hgap A hA
    (finiteTestKernel W a l f) (finiteTestKernel_measurable W a ha l f hf)
  rwa [finiteTestKernel_mixed W a ha l f hf] at hh

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions

lemma centered_radius_le (a : ℝ) (ha : 0≤a) (θ : Angle) (l : ℕ) :
    Real.sin θ.1*Real.exp (-2*a*l)≤(fromDisk θ.1 0).im := by
  rw [fromDisk_zero_im]
  apply mul_le_of_le_one_right (Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2).le
  apply Real.exp_le_one_iff.mpr
  have hl : (0:ℝ)≤l := Nat.cast_nonneg _
  nlinarith

lemma centered_radius_pos (a : ℝ) (θ : Angle) (l : ℕ) :
    0<Real.sin θ.1*Real.exp (-2*a*l) :=
  mul_pos (Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2) (Real.exp_pos _)

lemma centered_radius_strict (a : ℝ) (ha : 0<a) (θ : Angle) {l k : ℕ} (hlk : l<k) :
    Real.sin θ.1*Real.exp (-2*a*k)<Real.sin θ.1*Real.exp (-2*a*l) := by
  apply mul_lt_mul_of_pos_left _ (Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2)
  apply Real.exp_lt_exp.mpr
  have hk : (l:ℝ)<k := by exact_mod_cast hlk
  nlinarith

lemma centeredTime_stopping (a : ℝ) (ha : 1/4<a) (θ : Angle) (l : ℕ) :
    IsStoppingTime rawFiltration (fun b : ExactSLEGenerator.Driver=>levelTime a θ.1 b.1 l) := by
  have he : (fun b : ExactSLEGenerator.Driver=>levelTime a θ.1 b.1 l)=fun b=>
      radialTime a b.1 (fromDisk θ.1 0) (Real.sin θ.1*Real.exp (-2*a*l)) := by
    funext b
    exact levelTime_radialTime a θ.1 θ.2.1 θ.2.2 b.1 b.1.continuous l
  rw [he]
  exact radialTime_stopping a (by linarith) _
    (by rw [fromDisk_zero_im]; exact Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2)
    _ (centered_radius_pos a θ l) (centered_radius_le a (by linarith) θ l)

lemma centeredTime_monotone (a : ℝ) (ha : 1/4<a) (θ : Angle)
    (b : ExactSLEGenerator.Driver) : Monotone (levelTime a θ.1 b.1) := by
  intro l k hlk
  rcases hlk.eq_or_lt with rfl|hlk
  · exact le_rfl
  simp only [levelTime_radialTime a θ.1 θ.2.1 θ.2.2 b.1 b.1.continuous]
  exact radialTime_antitone a (by linarith) _
    (by rw [fromDisk_zero_im]; exact Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2)
    _ _ (centered_radius_pos a θ k) (centered_radius_strict a (by linarith) θ hlk).le
    (centered_radius_le a (by linarith) θ l) b

lemma centeredMass_monotone (a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    (b : ExactSLEGenerator.Driver) (hμ : Monotone (fun v=>μ v b)) (θ : Angle) :
    Monotone (fun l=>centeredMass a μ l (θ,b)) := by
  intro l k hlk
  exact Measure.le_iff'.mp (diskMass_mono
    (hμ (centeredTime_monotone a ha θ b hlk)) a θ.1) _

lemma centeredMass_raw_measurable (a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)] (θ : Angle) (l : ℕ)
    (hμ : Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
      (fun b=>μ (levelTime a θ.1 b.1 l) b)) :
    Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
      (fun b=>centeredMass a μ l (θ,b)) := by
  let : MeasurableSpace ExactSLEGenerator.Driver := (centeredTime_stopping a ha θ l).measurableSpace
  have hn := diskMass_joint_measurable a (fun _ : ExactSLEGenerator.Driver=>θ) measurable_const
    (fun b : ExactSLEGenerator.Driver=>μ (levelTime a θ.1 b.1 l) b) hμ
  exact (Measure.measurable_coe Metric.isClosed_closedBall.measurableSet).comp hn

 
lemma centered_laws_lintegral_consistent (W : Measure ExactSLEGenerator.Driver)
    [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver)=>b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (θ : Angle) {l k : ℕ} (hlk : l≤k)
    (f : ExactSLEGenerator.Driver→ℝ≥0∞)
    (hf : Measurable[(centeredTime_stopping a ha θ l).measurableSpace] f) :
    (∫⁻b,f b∂radialLaw W a (fromDisk θ.1 0) (Real.sin θ.1*Real.exp (-2*a*k)))=
      ∫⁻b,f b∂radialLaw W a (fromDisk θ.1 0) (Real.sin θ.1*Real.exp (-2*a*l)) := by
  rcases hlk.eq_or_lt with rfl|hlk
  · rfl
  obtain ⟨_,_,hS,he⟩ := finite_radial_laws_consistent W hW a ha _
    (by rw [fromDisk_zero_im]; exact Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2)
    _ _ (centered_radius_pos a θ k) (centered_radius_strict a (by linarith) θ hlk)
    (centered_radius_le a (by linarith) θ l)
  have heS : (fun b : ExactSLEGenerator.Driver=>levelTime a θ.1 b.1 l)=fun b=>
      radialTime a b.1 (fromDisk θ.1 0) (Real.sin θ.1*Real.exp (-2*a*l)) := by
    funext b
    exact levelTime_radialTime a θ.1 θ.2.1 θ.2.2 b.1 b.1.continuous l
  have hm : (centeredTime_stopping a ha θ l).measurableSpace=hS.measurableSpace := by
    congr 1
  have hf' : Measurable[hS.measurableSpace] f := by rwa [hm] at hf
  have hme : (radialLaw W a (fromDisk θ.1 0) (Real.sin θ.1*Real.exp (-2*a*k))).trim
      hS.measurableSpace_le =
      (radialLaw W a (fromDisk θ.1 0) (Real.sin θ.1*Real.exp (-2*a*l))).trim
      hS.measurableSpace_le := by
    refine @Measure.ext _ hS.measurableSpace _ _ (fun U hU=> ?_)
    rw [trim_measurableSet_eq _ hU,trim_measurableSet_eq _ hU]
    exact he U hU
  calc
    _ = ∫⁻b,f b∂(radialLaw W a (fromDisk θ.1 0)
        (Real.sin θ.1*Real.exp (-2*a*k))).trim hS.measurableSpace_le :=
      (lintegral_trim hS.measurableSpace_le hf').symm
    _ = _ := by rw [hme,lintegral_trim hS.measurableSpace_le hf']

lemma finiteAngleLaw_lintegral_consistent (W : Measure ExactSLEGenerator.Driver)
    [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver)=>b.1 t) W)
    (a : ℝ) (ha : 1/4<a) {l k : ℕ} (hlk : l≤k)
    (f : Angle×ExactSLEGenerator.Driver→ℝ≥0∞) (hf : Measurable f)
    (hr : ∀θ,Measurable[(centeredTime_stopping a ha θ l).measurableSpace] (fun b=>f (θ,b))) :
    (∫⁻p,f p∂finiteAngleLaw W a k)=∫⁻p,f p∂finiteAngleLaw W a l := by
  rw [finiteAngleLaw_lintegral W a ha k f hf,finiteAngleLaw_lintegral W a ha l f hf]
  exact lintegral_congr (fun θ=>centered_laws_lintegral_consistent W hW a ha θ hlk _ (hr θ))

 

theorem finiteMoment_monotone (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver)=>b.1 t) W)
    (a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    (hμ : Measurable (fun p : ℝ≥0∞×ExactSLEGenerator.Driver=>μ p.1 p.2))
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)]
    (hμraw : ∀l θ,Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
      (fun b=>μ (levelTime a θ.1 b.1 l) b))
    (hmono : ∀ᵐ b∂W,Monotone (fun v=>μ v b)) (m : ℕ) :
    Monotone (finiteMoment W a μ m) := by
  intro l k hlk
  rw [finiteMoment,←finiteAngleLaw_lintegral_consistent W hW a ha hlk _
    ((centeredMass_measurable a ha μ hμ l).pow_const m)
    (fun θ=>(centeredMass_raw_measurable a ha μ θ l (hμraw l θ)).pow_const m)]
  apply lintegral_mono_ae
  have hb : ∀ᵐ p ∂(angleLaw a).prod W,Monotone (fun v=>μ v p.2) :=
    Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hmono
  filter_upwards [(finiteAngleLaw_absolutelyContinuous W a k).ae_le hb] with p hp
  exact pow_le_pow_left' (centeredMass_monotone a ha μ p.2 hp p.1 hlk) m

end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator CenteredMoments LoewnerScaling

lemma raw_stopped_function_congr {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {F : GDriver→E} (hF : Measurable[hS.measurableSpace] F)
    {b c : GDriver} {u : ℝ≥0} (hb : S b≤u) (h : ∀v≤u,b.1 v=c.1 v) : F b=F c := by
  have hh := raw_stopped_event_congr hS (hF (measurableSet_singleton (F b))) hb h
  have hc := hh.mp (show b∈F ⁻¹' {F b} from rfl)
  exact hc.symm

 

def finiteStoppedTest (S : GDriver→ℝ≥0∞) (F : GDriver→ℝ≥0∞) (b : GDriver) : ℝ≥0∞ :=
  if S b=∞ then 0 else F (pastDriver (S b).toNNReal b)

lemma finiteStoppedTest_raw_measurable {S : GDriver→ℝ≥0∞}
    (hS : IsStoppingTime rawFiltration S) (F : GDriver→ℝ≥0∞) (hF : Measurable F) :
    Measurable[hS.measurableSpace] (finiteStoppedTest S F) := by
  exact Measurable.ite (hS.measurable (measurableSet_singleton ∞)) measurable_const
    (hF.comp (pastDriver_stopping_measurable S hS))

 

lemma normalized_levelTime_restart (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (σ : ℝ) (hσ : 0<σ) (hσz : σ≤z.im) (l : ℕ) (b : GDriver)
    (hb : radialTime a b.1 z σ≠∞) :
    let S := fun c : GDriver=>radialTime a c.1 z σ
    let w := radialPoint a z σ b
    S b + (‖w.1‖₊:ℝ≥0∞)^2 * levelTime a (pointAngle w).1
      (normalizeDriver w (restartAt S b)).1 l = radialTime a b.1 z (σ*Real.exp (-2*a*l)) := by
  dsimp only
  let S := fun c : GDriver=>radialTime a c.1 z σ
  let w := radialPoint a z σ b
  have hs := (pointAngle w).2.1
  have hsπ := (pointAngle w).2.2
  have hq : Real.exp (-2*a*l)≤1 := Real.exp_le_one_iff.mpr (by
    have hl : (0:ℝ)≤l := Nat.cast_nonneg l
    nlinarith)
  have hc := radialTime_scaled a (c:=‖w.1‖₊) (point_norm_pos w)
    (restartAt S b).1.continuous (fromDisk (pointAngle w).1 0)
    (Real.sin (pointAngle w).1*Real.exp (-2*a*l))
  have hr : ‖w.1‖*(Real.sin (pointAngle w).1*Real.exp (-2*a*l))=w.1.im*Real.exp (-2*a*l) := by
    rw [sin_pointAngle]
    field_simp [(point_norm_pos w).ne']
  simp only [coe_nnnorm] at hc
  rw [norm_mul_fromDisk_pointAngle,hr] at hc
  change S b+(‖w.1‖₊:ℝ≥0∞)^2*levelTime a (pointAngle w).1
    (normalizeDriver w (restartAt S b)).1 l=_
  rw [levelTime_radialTime a (pointAngle w).1 hs hsπ _
    (normalizeDriver w (restartAt S b)).1.continuous]
  change S b+(‖w.1‖₊:ℝ≥0∞)^2*radialTime a (scaled ‖w.1‖₊ (restartAt S b).1)
    (fromDisk (pointAngle w).1 0) (Real.sin (pointAngle w).1*Real.exp (-2*a*l))=_
  rw [hc]
  have hh := radialTime_restart a ha z hz σ (σ*Real.exp (-2*a*l))
    (mul_pos hσ (Real.exp_pos _)) (mul_le_of_le_one_right hσ.le hq) hσz b hb
  dsimp only at hh
  rw [←radialPoint_eq a ha z hz σ hσ hσz b hb,mul_div_cancel_left₀ _ hσ.ne'] at hh
  simpa only [S,ENNReal.coe_toNNReal hb,restartAt,w] using hh

lemma normalizedTest_history_congr (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (σ : ℝ) (hσ : 0<σ) (hσz : σ≤z.im) (l : ℕ)
    (f : Angle×GDriver→ℝ≥0∞)
    (hfraw : ∀θ,Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
      (fun b : GDriver=>f (θ,b)))
    {b c : GDriver} {u : ℝ≥0}
    (hb : radialTime a b.1 z (σ*Real.exp (-2*a*l))≤u)
    (hbc : ∀v≤u,b.1 v=c.1 v) :
    normalizedTest a z σ f b=normalizedTest a z σ f c := by
  let S := fun c : GDriver=>radialTime a c.1 z σ
  let T := fun c : GDriver=>radialTime a c.1 z (σ*Real.exp (-2*a*l))
  have ha0 : 0<a := by linarith
  have hq : Real.exp (-2*a*l)≤1 := Real.exp_le_one_iff.mpr (by
    have hl : (0:ℝ)≤l := Nat.cast_nonneg l
    nlinarith)
  have hST := radialTime_antitone a ha0 z hz (σ*Real.exp (-2*a*l)) σ
    (mul_pos hσ (Real.exp_pos _)) (mul_le_of_le_one_right hσ.le hq) hσz b
  have hS := radialTime_stopping a ha0 z hz σ hσ hσz
  have hSb : S b≤u := hST.trans hb
  have hbf : S b≠∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hSb
  have hbs : (S b).toNNReal≤u := ENNReal.coe_le_coe.mp (by
    simpa only [ENNReal.coe_toNNReal hbf] using hSb)
  have hSc : S c=S b := by
    have hh := raw_stop_congr hS (ENNReal.coe_toNNReal hbf).symm
      (fun v hv=>hbc v (hv.trans hbs))
    simpa only [ENNReal.coe_toNNReal hbf] using hh
  have hw : radialPoint a z σ b=radialPoint a z σ c :=
    raw_stopped_function_congr hS (radialPoint_raw_measurable a ha z hz σ hσ hσz) hSb hbc
  let w := radialPoint a z σ b
  let b' := normalizeDriver w (restartAt S b)
  let c' := normalizeDriver w (restartAt S c)
  let L := levelTime a (pointAngle w).1 b'.1 l
  have hsum : S b+(‖w.1‖₊:ℝ≥0∞)^2*L=T b :=
    normalized_levelTime_restart a ha0 z hz σ hσ hσz l b hbf
  have hLf : L≠∞ := by
    intro he
    have hn : (‖w.1‖₊:ℝ≥0∞)^2≠0 := pow_ne_zero 2 (by
      exact ENNReal.coe_ne_zero.mpr (NNReal.coe_ne_zero.mp (point_norm_pos w).ne'))
    rw [he,ENNReal.mul_top hn,add_top] at hsum
    exact (ne_top_of_le_ne_top ENNReal.coe_ne_top hb) hsum.symm
  have htime : (S b).toNNReal+‖w.1‖₊^2*L.toNNReal≤u := by
    apply ENNReal.coe_le_coe.mp
    simp only [ENNReal.coe_add,ENNReal.coe_mul,ENNReal.coe_pow,ENNReal.coe_toNNReal hLf,
      ENNReal.coe_toNNReal hbf]
    rw [hsum]
    exact hb
  have hhistory : ∀v≤L.toNNReal,b'.1 v=c'.1 v := by
    intro v hv
    change ‖w.1‖⁻¹*((restartAt S b).1 (‖w.1‖₊^2*v))=
      ‖w.1‖⁻¹*((restartAt S c).1 (‖w.1‖₊^2*v))
    simp only [restartAt,restart_apply,hSc]
    have ht : (S b).toNNReal+‖w.1‖₊^2*v≤u :=
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hv (by positivity))).trans htime
    rw [hbc _ ht,hbc _ hbs]
  have hh := raw_stopped_function_congr (centeredTime_stopping a ha (pointAngle w) l)
    (hfraw (pointAngle w)) (le_of_eq (ENNReal.coe_toNNReal hLf).symm) hhistory
  change f (pointAngle w,b')=f (pointAngle (radialPoint a z σ c),
    normalizeDriver (radialPoint a z σ c) (restartAt S c))
  rw [←hw]
  exact hh

 

lemma finiteStoppedTest_normalizedTest_eq (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (σ : ℝ) (hσ : 0<σ) (hσz : σ≤z.im) (l : ℕ)
    (f : Angle×GDriver→ℝ≥0∞)
    (hfraw : ∀θ,Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
      (fun b : GDriver=>f (θ,b)))
    (b : GDriver) (hb : radialTime a b.1 z (σ*Real.exp (-2*a*l))≠∞) :
    finiteStoppedTest (fun c : GDriver=>radialTime a c.1 z (σ*Real.exp (-2*a*l)))
      (normalizedTest a z σ f) b=normalizedTest a z σ f b := by
  rw [finiteStoppedTest,ite_eq_right hb]
  exact (normalizedTest_history_congr a ha z hz σ hσ hσz l f hfraw
    (le_of_eq (ENNReal.coe_toNNReal hb).symm) (fun v hv=>(pastDriver_eq _ b v hv).symm)).symm

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal Classical
namespace SLEExactGauge.CompactSequence

 
def initialVector {E : Type*} (n : ℕ) (x : ℕ→E) : Fin (n+1)→E := fun i=>x i

lemma continuous_initialVector {E : Type*} [TopologicalSpace E] (n : ℕ) :
    Continuous (initialVector (E:=E) n) := continuous_pi (fun _=>continuous_apply _)

lemma measurable_initialVector {E : Type*} [MeasurableSpace E] (n : ℕ) :
    Measurable (initialVector (E:=E) n) := Measurable.of_eval (fun _=>measurable_pi_apply _)

 

theorem exists_sequence_law {E Ω : Type*} [TopologicalSpace E] [CompactSpace E]
    [T2Space E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω]
    (P : ℕ→Measure Ω) [∀n,IsProbabilityMeasure (P n)]
    (X : ℕ→Ω→E) (hX : ∀n,Measurable (X n))
    (hcons : ∀n k,n≤k →
      (P k).map (fun ω : Ω=>fun i : Fin (n+1)=>X i ω)=
      (P n).map (fun ω : Ω=>fun i : Fin (n+1)=>X i ω)) :
    ∃Q : Measure (ℕ→E),IsProbabilityMeasure Q ∧
      ∀n,Q.map (initialVector n)=(P n).map (fun ω : Ω=>fun i : Fin (n+1)=>X i ω) := by
  have hXm : Measurable (fun ω : Ω=>fun n=>X n ω) := Measurable.of_eval hX
  let ν : ℕ→ProbabilityMeasure (ℕ→E) := fun n=>
    ⟨(P n).map (fun ω : Ω=>fun i=>X i ω),inferInstance⟩
  obtain ⟨Q,hQ⟩ := exists_clusterPt_of_compactSpace (Filter.map ν atTop)
  refine ⟨Q,Q.prop,?_⟩
  intro n
  have he (k : ℕ) (hkn : n≤k) :
      (ν k).map (initialVector n)=
        (ν n).map (initialVector n) := by
    apply ProbabilityMeasure.toMeasure_injective
    change ((P k).map (fun ω : Ω=>fun i=>X i ω)).map (initialVector n)=
      ((P n).map (fun ω : Ω=>fun i=>X i ω)).map (initialVector n)
    rw [Measure.map_map (measurable_initialVector n) hXm,Measure.map_map (measurable_initialVector n) hXm]
    exact hcons n k hkn
  have hc : IsClosed {q : ProbabilityMeasure (ℕ→E) |
      q.map (initialVector n)=(ν n).map (initialVector n)} :=
    isClosed_eq (ProbabilityMeasure.continuous_map (continuous_initialVector n)) continuous_const
  have hq := hc.mem_of_mapClusterPt hQ (Filter.eventually_atTop.mpr ⟨n,he⟩)
  have hqm := congrArg ProbabilityMeasure.toMeasure hq
  change Q.toMeasure.map (initialVector n)=
    ((P n).map (fun ω : Ω=>fun i=>X i ω)).map (initialVector n) at hqm
  rw [Measure.map_map (measurable_initialVector n) hXm] at hqm
  exact hqm

 
lemma lintegral_initialVector {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (Q : Measure (ℕ→E)) (P : Measure Ω) (X : ℕ→Ω→E)
    (hX : ∀n,Measurable (X n)) (n : ℕ)
    (hQ : Q.map (initialVector n)=P.map (fun ω : Ω=>fun i : Fin (n+1)=>X i ω))
    (f : (Fin (n+1)→E)→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻x,f (initialVector n x)∂Q)=∫⁻ω,f (fun i=>X i ω)∂P := by
  rw [←lintegral_map hf (measurable_initialVector n),hQ,
    lintegral_map hf (Measurable.of_eval (fun i=>hX i))]

lemma lintegral_coordinate {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (Q : Measure (ℕ→E)) (P : Measure Ω) (X : ℕ→Ω→E)
    (hX : ∀n,Measurable (X n)) (n : ℕ)
    (hQ : Q.map (initialVector n)=P.map (fun ω : Ω=>fun i : Fin (n+1)=>X i ω))
    (f : E→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻x,f (x n)∂Q)=∫⁻ω,f (X n ω)∂P :=
  lintegral_initialVector Q P X hX n hQ (fun x=>f (x ⟨n,by omega⟩))
    (hf.comp (measurable_pi_apply _))

end SLEExactGauge.CompactSequence
end
end

end OAI
