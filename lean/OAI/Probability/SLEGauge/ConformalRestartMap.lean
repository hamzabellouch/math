import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.OptionalGreen

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen

lemma literal_parameter (a : ℝ) : Target.a (2/a)=a := div_div_cancel₀ (by norm_num : (2:ℝ)≠0)

lemma literal_flow (a : ℝ) (b : GDriver) (z : ℂ) (t : ℝ≥0) :
    LiteralTrace.flow (2/a) (driverHomeomorph.symm b) z t=loewnerMap a b.1 t z := by
  rw [←flow_eq_literal,flow_eq_loewnerMap,literal_parameter,driverHomeomorph.apply_symm_apply]

lemma literal_surviving (a : ℝ) (b : GDriver) (z : ℂ) (t : ℝ≥0) :
    LiteralTrace.Surviving (2/a) (driverHomeomorph.symm b) z t ↔ alive a b.1 t z := by
  rw [←surviving_eq,surviving_iff_alive,literal_parameter,driverHomeomorph.apply_symm_apply]

 
def inverseMap (a : ℝ) (b : GDriver) (s : ℝ≥0) (w : ℂ) : ℂ :=
  LiteralTrace.inverseFlow (2/a) (driverHomeomorph.symm b) s (w+(b.1 s:ℂ))

lemma inverseMap_alive {a : ℝ} (ha : 0<a) (b : GDriver) (s : ℝ≥0)
    {w : ℂ} (hw : 0<w.im) : alive a b.1 s (inverseMap a b s w) := by
  apply (literal_surviving a b _ s).mp
  apply LiteralTrace.inverseFlow_surviving (by positivity) _ s.coe_nonneg
  simpa only [Complex.add_im,Complex.ofReal_im,add_zero] using hw

lemma alive_initial_im {a : ℝ} {b : ℝ≥0→ℝ} {s : ℝ≥0} {z : ℂ}
    (hz : alive a b s z) : 0<z.im := by
  obtain ⟨f,hf⟩ := hz
  simpa only [hf.1] using (hf.2 0 ⟨le_rfl,s.coe_nonneg⟩).1

lemma loewnerMap_im_pos {a : ℝ} {b : ℝ≥0→ℝ} {s : ℝ≥0} {z : ℂ}
    (hz : alive a b s z) : 0<(loewnerMap a b s z).im := by
  obtain ⟨f,hf⟩ := hz
  rw [loewnerMap_eq hf]
  exact (hf.2 s ⟨s.coe_nonneg,le_rfl⟩).1

lemma centered_inverseMap {a : ℝ} (ha : 0<a) (b : GDriver) (s : ℝ≥0)
    {w : ℂ} (hw : 0<w.im) :
    loewnerMap a b.1 s (inverseMap a b s w)-(b.1 s:ℂ)=w := by
  rw [←literal_flow,inverseMap,LiteralTrace.flow_inverseFlow (by positivity) _ s.coe_nonneg
    (by simpa only [Complex.add_im,Complex.ofReal_im,add_zero] using hw),add_sub_cancel_right]

lemma inverseMap_centered (a : ℝ) (b : GDriver) (s : ℝ≥0) {z : ℂ}
    (hz : alive a b.1 s z) :
    inverseMap a b s (loewnerMap a b.1 s z-(b.1 s:ℂ))=z := by
  rw [inverseMap,sub_add_cancel,←literal_flow]
  exact LiteralTrace.inverseFlow_flow s.coe_nonneg ((literal_surviving a b z s).mpr hz)

lemma inverseMap_hasStrictDerivAt {a : ℝ} (ha : 0<a) (b : GDriver) (s : ℝ≥0)
    {w : ℂ} (hw : 0<w.im) :
    HasStrictDerivAt (inverseMap a b s)
      (deriv (loewnerMap a b.1 s) (inverseMap a b s w))⁻¹ w := by
  have h := (LiteralTrace.inverseFlow_hasStrictDerivAt (by positivity : 0<2/a)
    (driverHomeomorph.symm b) s.coe_nonneg
    (show 0<(w+(b.1 s:ℂ)).im by simpa using hw)).scomp w
      ((hasStrictDerivAt_id w).add_const (b.1 s:ℂ))
  simp only [literal_flow, Function.comp_def, id_eq, one_smul] at h
  convert! h using 1

lemma deriv_inverseMap {a : ℝ} (ha : 0<a) (b : GDriver) (s : ℝ≥0)
    {w : ℂ} (hw : 0<w.im) :
    deriv (inverseMap a b s) w=(deriv (loewnerMap a b.1 s) (inverseMap a b s w))⁻¹ :=
  (inverseMap_hasStrictDerivAt ha b s hw).hasDerivAt.deriv

lemma deriv_inverseMap_ne_zero {a : ℝ} (ha : 0<a) (b : GDriver) (s : ℝ≥0)
    {w : ℂ} (hw : 0<w.im) : deriv (inverseMap a b s) w≠0 := by
  rw [deriv_inverseMap ha b s hw]
  exact inv_ne_zero (deriv_loewnerMap_ne_zero b.1.continuous (inverseMap_alive ha b s hw))

 
def inverseUpper (a : ℝ) (ha : 0<a) (b : GDriver) (s : ℝ≥0) (w : UpperPlane) : UpperPlane :=
  ⟨inverseMap a b s w.1,alive_initial_im (inverseMap_alive ha b s w.2)⟩

lemma continuous_inverseUpper (a : ℝ) (ha : 0<a) (b : GDriver) (s : ℝ≥0) :
    Continuous (inverseUpper a ha b s) := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro w
  exact (inverseMap_hasStrictDerivAt ha b s w.2).hasDerivAt.continuousAt.comp
    continuous_subtype_val.continuousAt

lemma inverseUpper_injective (a : ℝ) (ha : 0<a) (b : GDriver) (s : ℝ≥0) :
    Function.Injective (inverseUpper a ha b s) := by
  intro u v h
  apply Subtype.ext
  have hh := congrArg (fun z : UpperPlane => loewnerMap a b.1 s z.1-(b.1 s:ℂ)) h
  simpa only [inverseUpper,centered_inverseMap ha b s u.2,centered_inverseMap ha b s v.2] using hh

 
def restartHomeomorph (a : ℝ) (ha : 0<a) (b : GDriver) (s : ℝ≥0) :
    UpperPlane ≃ₜ {z : UpperPlane // alive a b.1 s z.1} where
  toFun w := ⟨inverseUpper a ha b s w,inverseMap_alive ha b s w.2⟩
  invFun z := ⟨loewnerMap a b.1 s z.1.1-(b.1 s:ℂ),by
    simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using loewnerMap_im_pos z.2⟩
  left_inv w := by
    apply Subtype.ext
    exact centered_inverseMap ha b s w.2
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact inverseMap_centered a b s z.2
  continuous_toFun := (continuous_inverseUpper a ha b s).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro z
    have hc : ContinuousAt (fun z : {z : UpperPlane // alive a b.1 s z.1} => z.1.1) z :=
      (continuous_subtype_val.comp continuous_subtype_val).continuousAt
    exact ((hasDerivAt_loewnerMap b.1.continuous z.2).continuousAt.comp_of_eq hc rfl).sub continuousAt_const

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen

abbrev AliveData (a : ℝ) := {p : ℝ≥0×(GDriver×UpperPlane) //
  alive a p.2.1.1 p.1 p.2.2.1}

def centeredData (a : ℝ) (p : AliveData a) : ℝ≥0×(GDriver×UpperPlane) :=
  (p.1.1,(p.1.2.1,⟨loewnerMap a p.1.2.1.1 p.1.1 p.1.2.2.1-(p.1.2.1.1 p.1.1:ℂ),by
    simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using loewnerMap_im_pos p.2⟩))

lemma measurable_centeredData (a : ℝ) (ha : 1/4<a) : Measurable (centeredData a) := by
  have hv : Measurable (fun p : ℝ≥0×(GDriver×UpperPlane) => (p.2.1.1 p.1:ℂ)) :=
    (Complex.continuous_ofReal.comp (continuous_subtype_val.comp (continuous_fst.comp
      continuous_snd) |>.eval continuous_fst)).measurable
  exact (measurable_fst.comp measurable_subtype_coe).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_subtype_coe)).prodMk
      (((loewnerMap_time_joint_measurable a ha).comp measurable_subtype_coe).sub
        (hv.comp measurable_subtype_coe) |>.subtype_mk))

lemma centeredData_injective (a : ℝ) : Function.Injective (centeredData a) := by
  rintro ⟨⟨s,b,z⟩,hz⟩ ⟨⟨t,c,w⟩,hw⟩ h
  have ht : s=t := congrArg Prod.fst h
  have hc : b=c := congrArg (fun p => p.2.1) h
  subst t; subst c
  have hz' : loewnerMap a b.1 s z.1-(b.1 s:ℂ)=loewnerMap a b.1 s w.1-(b.1 s:ℂ) :=
    congrArg (fun p => p.2.2.1) h
  have hzw := congrArg (inverseMap a b s) hz'
  rw [inverseMap_centered a b s hz,inverseMap_centered a b s hw] at hzw
  have : z=w := Subtype.ext hzw
  subst w
  rfl

 
lemma inverseUpper_joint_measurable (a : ℝ) (ha : 1/4<a) :
    Measurable (fun p : ℝ≥0×(GDriver×UpperPlane) =>
      inverseUpper a (lt_trans (by norm_num) ha) p.2.1 p.1 p.2.2) := by
  have ha0 : 0<a := lt_trans (by norm_num) ha
  have : PolishSpace GDriver :=
    (isClosed_eq (continuous_eval_const 0) continuous_const).polishSpace
  have : PolishSpace UpperPlane := upperPlane_open.polishSpace
  have : StandardBorelSpace (AliveData a) := (measurableSet_alive_joint a ha).standardBorel
  let inv : (ℝ≥0×(GDriver×UpperPlane))→AliveData a := fun p =>
    ⟨(p.1,(p.2.1,inverseUpper a ha0 p.2.1 p.1 p.2.2)),inverseMap_alive ha0 _ _ p.2.2.2⟩
  have hi : Measurable inv := by
    apply ((measurable_centeredData a ha).measurableEmbedding (centeredData_injective a)).measurable_comp_iff.mp
    have he : centeredData a ∘ inv=id := by
      funext p
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      apply Subtype.ext
      exact centered_inverseMap ha0 _ _ p.2.2.2
    rw [he]
    exact measurable_id
  exact (measurable_subtype_coe.comp hi).snd.snd

lemma norm_deriv_inverseMap_eq_exp (a : ℝ) (ha : 0<a) (b : GDriver)
    (s : ℝ≥0) (w : UpperPlane) :
    ‖deriv (inverseMap a b s) w.1‖=
      Real.exp (-(killedState a s b (inverseUpper a ha b s w).1).2) := by
  simp only [inverseUpper]
  rw [deriv_inverseMap ha b s w.2,norm_inv,killedState,
    ite_eq_left (inverseMap_alive ha b s w.2),actualState,Real.exp_neg,Real.exp_log]
  exact norm_pos_iff.mpr (deriv_loewnerMap_ne_zero b.1.continuous (inverseMap_alive ha b s w.2))

 
lemma norm_deriv_inverseMap_joint_measurable (a : ℝ) (ha : 1/4<a) :
    Measurable (fun p : ℝ≥0×(GDriver×UpperPlane) =>
      ‖deriv (inverseMap a p.2.1 p.1) p.2.2.1‖) := by
  simp_rw [norm_deriv_inverseMap_eq_exp a (lt_trans (by norm_num) ha)]
  exact (((killedState_time_joint_measurable a ha).comp
    (measurable_fst.prodMk (measurable_snd.fst.prodMk
      (inverseUpper_joint_measurable a ha)))).snd.neg).exp

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.Conformal

def realDerivative (v : ℂ) : ℂ→L[ℝ]ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ v).restrictScalars ℝ

lemma det_realDerivative (v : ℂ) : (realDerivative v).det=‖v‖^2 := by
  simp [realDerivative,ContinuousLinearMap.det,LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq,Complex.normSq_eq_norm_sq]

lemma lintegral_image_complex {f : ℂ→ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hd : ∀z∈s,DifferentiableAt ℂ f z) (hi : InjOn f s) (g : ℂ→ℝ≥0∞) :
    (∫⁻z in f '' s,g z∂volume)=
      ∫⁻w in s,ENNReal.ofReal (‖deriv f w‖^2)*g (f w)∂volume := by
  have hf (z : ℂ) (hz : z∈s) : HasFDerivWithinAt f (realDerivative (deriv f z)) s z :=
    ((hd z hz).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  simpa only [det_realDerivative,abs_pow, abs_norm] using
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hf hi g

 

lemma map_withDensity_composed {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {e : X→Y} (he : Measurable e) {f : Y→ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (fun x => f (e x))).map e=(μ.map e).withDensity f := by
  ext A hA
  rw [Measure.map_apply he hA,withDensity_apply _ (he hA),
    withDensity_apply _ hA,Measure.restrict_map he hA,lintegral_map hf he]

end SLEExactGauge.Conformal
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen

 

def upperExtend (f : UpperPlane→ℝ≥0∞) (z : ℂ) : ℝ≥0∞ :=
  if hz : 0<z.im then f ⟨z,hz⟩ else 0

@[simp] lemma upperExtend_coe (f : UpperPlane→ℝ≥0∞) (z : UpperPlane) :
    upperExtend f z.1=f z := dite_eq_left z.2

lemma image_inverseMap_upper (a : ℝ) (ha : 0<a) (b : GDriver) (s : ℝ≥0) :
    inverseMap a b s '' {w : ℂ | 0<w.im}=
      Subtype.val '' {z : UpperPlane | alive a b.1 s z.1} := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨inverseUpper a ha b s ⟨w,hw⟩,inverseMap_alive ha b s hw,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    refine ⟨loewnerMap a b.1 s z.1-(b.1 s:ℂ),?_,inverseMap_centered a b s hz⟩
    simpa only [mem_ofPred_eq,Complex.sub_im,Complex.ofReal_im,sub_zero] using
      loewnerMap_im_pos hz

lemma inverseMap_injOn_upper (a : ℝ) (ha : 0<a) (b : GDriver) (s : ℝ≥0) :
    InjOn (inverseMap a b s) {w : ℂ | 0<w.im} := by
  intro u hu v hv huv
  have h := congrArg (fun z => loewnerMap a b.1 s z-(b.1 s:ℂ)) huv
  simpa only [centered_inverseMap ha b s hu,centered_inverseMap ha b s hv] using h

 

theorem inverseUpper_lintegral_area (a : ℝ) (ha : 0<a) (b : GDriver) (s : ℝ≥0)
    (f : UpperPlane→ℝ≥0∞) :
    (∫⁻w : UpperPlane, ENNReal.ofReal (‖deriv (inverseMap a b s) w.1‖^2)*
      f (inverseUpper a ha b s w) ∂upperArea)=
    ∫⁻z in {z : UpperPlane | alive a b.1 s z.1},f z∂upperArea := by
  have h := Conformal.lintegral_image_complex upperPlane_open.measurableSet
    (fun w hw => (inverseMap_hasStrictDerivAt ha b s hw).hasDerivAt.differentiableAt)
    (inverseMap_injOn_upper a ha b s) (upperExtend f)
  rw [image_inverseMap_upper a ha b s] at h
  have hleft := setLIntegral_subtype (μ:=(volume : Measure ℂ))
    upperPlane_open.measurableSet {z : UpperPlane | alive a b.1 s z.1} (upperExtend f)
  have hright := lintegral_subtype_comap (μ:=(volume : Measure ℂ))
    upperPlane_open.measurableSet (fun w =>
      ENNReal.ofReal (‖deriv (inverseMap a b s) w‖^2)*upperExtend f (inverseMap a b s w))
  have hh := hright.trans (h.symm.trans hleft.symm)
  have he (w : UpperPlane) : upperExtend f (inverseMap a b s w.1)=
      f (inverseUpper a ha b s w) := dite_eq_left (alive_initial_im (inverseMap_alive ha b s w.2))
  simp only [upperExtend_coe, he] at hh
  convert! hh using 1

 
theorem map_inverseUpper_area (a : ℝ) (ha : 1/4<a) (b : GDriver) (s : ℝ≥0) :
    (upperArea.withDensity (fun w : UpperPlane =>
       ENNReal.ofReal (‖deriv (inverseMap a b s) w.1‖^2))).map
        (inverseUpper a (lt_trans (by norm_num) ha) b s)=
      upperArea.restrict {z : UpperPlane | alive a b.1 s z.1} := by
  let ha0 : 0<a := lt_trans (by norm_num) ha
  let J := inverseUpper a ha0 b s
  have hJ : Measurable J := (continuous_inverseUpper a ha0 b s).measurable
  have hsurv : MeasurableSet {z : UpperPlane | alive a b.1 s z.1} :=
    (measurableSet_alive_joint a ha).preimage
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  ext A hA
  rw [Measure.map_apply hJ hA,withDensity_apply _ (hJ hA),
    Measure.restrict_apply hA]
  have h := inverseUpper_lintegral_area a ha0 b s (A.indicator (fun _ =>1))
  have hi : (fun w : UpperPlane => ENNReal.ofReal (‖deriv (inverseMap a b s) w.1‖^2)*
      A.indicator (fun _ =>1) (J w))=
      (J ⁻¹' A).indicator (fun w => ENNReal.ofReal (‖deriv (inverseMap a b s) w.1‖^2)) := by
    funext w
    by_cases hw : J w ∈ A <;> simp [hw]
  change (∫⁻w : UpperPlane, ENNReal.ofReal (‖deriv (inverseMap a b s) w.1‖^2)*
      A.indicator (fun _ =>1) (J w) ∂upperArea)=_ at h
  rw [hi,lintegral_indicator (hJ hA),lintegral_indicator hA,
    setLIntegral_one,Measure.restrict_apply hA] at h
  exact h

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen

 
def restartWeight (a : ℝ) (b : GDriver) (s : ℝ≥0) (w : UpperPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (‖deriv (inverseMap a b s) w.1‖^(2-alpha a))

lemma restartWeight_pos (a : ℝ) (ha : 0<a) (b : GDriver) (s : ℝ≥0) (w : UpperPlane) :
    0<restartWeight a b s w := ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr (deriv_inverseMap_ne_zero ha b s w.2)) _)

lemma restartWeight_ne_top (a : ℝ) (b : GDriver) (s : ℝ≥0) (w : UpperPlane) :
    restartWeight a b s w≠∞ := ENNReal.ofReal_ne_top

lemma restartWeight_joint_measurable (a : ℝ) (ha : 1/4<a) :
    Measurable (fun p : ℝ≥0×(GDriver×UpperPlane) => restartWeight a p.2.1 p.1 p.2.2) :=
  ((norm_deriv_inverseMap_joint_measurable a ha).pow_const _).ennreal_ofReal

lemma restartWeight_measurable (a : ℝ) (ha : 1/4<a) (b : GDriver) (s : ℝ≥0) :
    Measurable (restartWeight a b s) := by
  have hin : Measurable (fun w : UpperPlane => (s,(b,w))) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hh := (restartWeight_joint_measurable a ha).comp hin
  change Measurable (fun w : UpperPlane => restartWeight a b s w) at hh
  exact hh

lemma green_jacobian_restart (a : ℝ) (ha : 0<a) (b : GDriver) (s t : ℝ≥0)
    (w : UpperPlane) :
    ENNReal.ofReal (‖deriv (inverseMap a b s) w.1‖^2)*
      ENNReal.ofReal (survivingGreen a (s+t) b (inverseUpper a ha b s w).1)=
      restartWeight a b s w*ENNReal.ofReal (survivingGreen a t (restart s b) w.1) := by
  have hi := inverseMap_alive ha b s w.2
  have hp : 0<‖deriv (inverseMap a b s) w.1‖ :=
    norm_pos_iff.mpr (deriv_inverseMap_ne_zero ha b s w.2)
  have hr : ‖deriv (loewnerMap a b.1 s) (inverseMap a b s w.1)‖ =
      ‖deriv (inverseMap a b s) w.1‖⁻¹ := by
    rw [deriv_inverseMap ha b s w.2,norm_inv,inv_inv]
  change ENNReal.ofReal (‖deriv (inverseMap a b s) w.1‖^2)*
      ENNReal.ofReal (survivingGreen a (s+t) b (inverseMap a b s w.1))=_
  rw [survivingGreen_restart a b s t hi,centered_inverseMap ha b s w.2,hr,
    ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hp.le) _),←mul_assoc,
    ←ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  rw [←Real.rpow_two,←Real.rpow_neg_eq_inv_rpow,←Real.rpow_add hp,←sub_eq_add_neg]
  rfl

 

theorem inverseUpper_lintegral_green (a : ℝ) (ha : 0<a) (b : GDriver) (s t : ℝ≥0)
    (f : UpperPlane→ℝ≥0∞) :
    (∫⁻w : UpperPlane,restartWeight a b s w*ENNReal.ofReal
      (survivingGreen a t (restart s b) w.1)*f (inverseUpper a ha b s w)∂upperArea)=
    ∫⁻z in {z : UpperPlane | alive a b.1 s z.1},
      ENNReal.ofReal (survivingGreen a (s+t) b z.1)*f z∂upperArea := by
  have h := inverseUpper_lintegral_area a ha b s
    (fun z => ENNReal.ofReal (survivingGreen a (s+t) b z.1)*f z)
  simpa only [←mul_assoc,green_jacobian_restart a ha b s t] using h

 

def restartPush (a : ℝ) (ha : 0<a) (b : GDriver) (s : ℝ≥0) (μ : Measure UpperPlane) :
    Measure UpperPlane := (μ.withDensity (restartWeight a b s)).map (inverseUpper a ha b s)

lemma restartPush_lintegral (a : ℝ) (ha : 1/4<a) (b : GDriver) (s : ℝ≥0)
    (μ : Measure UpperPlane) {f : UpperPlane→ℝ≥0∞} (hf : Measurable f) :
    (∫⁻z,f z∂restartPush a (lt_trans (by norm_num) ha) b s μ)=
      ∫⁻w,restartWeight a b s w*f (inverseUpper a (lt_trans (by norm_num) ha) b s w)∂μ := by
  have hJ := (continuous_inverseUpper a (lt_trans (by norm_num) ha) b s).measurable
  have hF : Measurable (fun w : UpperPlane =>
      f (inverseUpper a (lt_trans (by norm_num) ha) b s w)) := hf.comp hJ
  rw [restartPush,lintegral_map hf hJ]
  exact lintegral_withDensity_eq_lintegral_mul μ (restartWeight_measurable a ha b s) hF

 

theorem restartPush_survivingKernel (a : ℝ) (ha : 1/4<a) (b : GDriver) (s t : ℝ≥0) :
    restartPush a (lt_trans (by norm_num) ha) b s (survivingKernel a ha t (restart s b))=
      (survivingKernel a ha (s+t) b).restrict {z : UpperPlane | alive a b.1 s z.1} := by
  let ha0 : 0<a := lt_trans (by norm_num) ha
  let J := inverseUpper a ha0 b s
  have hJ : Measurable J := (continuous_inverseUpper a ha0 b s).measurable
  have hsurv : MeasurableSet {z : UpperPlane | alive a b.1 s z.1} :=
    (measurableSet_alive_joint a ha).preimage
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  ext A hA
  have h := inverseUpper_lintegral_green a ha0 b s t (A.indicator (fun _ =>1))
  have heL := restartPush_lintegral a ha b s (survivingKernel a ha t (restart s b))
    (measurable_const.indicator hA : Measurable (A.indicator (fun _ =>(1:ℝ≥0∞))))
  rw [lintegral_indicator hA,setLIntegral_one] at heL
  have hF : Measurable (fun w : UpperPlane => restartWeight a b s w*
      A.indicator (fun _ =>(1:ℝ≥0∞)) (inverseUpper a ha0 b s w)) :=
    (restartWeight_measurable a ha b s).mul ((measurable_const.indicator hA).comp hJ)
  rw [survivingKernel_apply,lintegral_withDensity_eq_lintegral_mul upperArea
    (survivingGreen_spatial_measurable a ha t (restart s b)).ennreal_ofReal hF] at heL
  have heR : (∫⁻z in {z : UpperPlane | alive a b.1 s z.1},
      ENNReal.ofReal (survivingGreen a (s+t) b z.1)*A.indicator (fun _ =>1) z∂upperArea)=
      ((survivingKernel a ha (s+t) b).restrict {z : UpperPlane | alive a b.1 s z.1}) A := by
    rw [survivingKernel_apply,Measure.restrict_apply hA,withDensity_apply _ (hA.inter hsurv)]
    calc
      _ = ∫⁻z in {z : UpperPlane | alive a b.1 s z.1},
          A.indicator (fun z => ENNReal.ofReal (survivingGreen a (s+t) b z.1)) z∂upperArea := by
        congr 1
        funext z
        by_cases hz : z∈A <;> simp [hz]
      _ = _ := by rw [lintegral_indicator hA,Measure.restrict_restrict hA]
  rw [←heR,←h]
  rw [survivingKernel_apply]
  simpa only [Pi.mul_apply,mul_left_comm,mul_assoc] using heL

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator

lemma inverseMap_driver_congr (a : ℝ) (ha : 0<a) {b c : GDriver} {s : ℝ≥0}
    (h : ∀ u ≤ s,b.1 u=c.1 u) {w : ℂ} (hw : 0<w.im) :
    inverseMap a b s w=inverseMap a c s w := by
  have hi := inverseMap_alive ha b s hw
  have hc := (alive_driver_congr h).mp hi
  have he : loewnerMap a c.1 s (inverseMap a b s w)-(c.1 s:ℂ)=w := by
    rw [←loewnerMap_driver_congr h,←h s le_rfl]
    exact centered_inverseMap ha b s hw
  have hj := inverseMap_centered a c s hc
  rw [he] at hj
  exact hj.symm

lemma inverseUpper_driver_congr (a : ℝ) (ha : 0<a) {b c : GDriver} {s : ℝ≥0}
    (h : ∀ u ≤ s,b.1 u=c.1 u) : inverseUpper a ha b s=inverseUpper a ha c s := by
  funext w
  apply Subtype.ext
  exact inverseMap_driver_congr a ha h w.2

lemma restartWeight_driver_congr (a : ℝ) (ha : 0<a) {b c : GDriver} {s : ℝ≥0}
    (h : ∀ u ≤ s,b.1 u=c.1 u) : restartWeight a b s=restartWeight a c s := by
  funext w
  simp only [restartWeight,deriv_inverseMap ha _ _ w.2,
    inverseMap_driver_congr a ha h w.2,loewnerMap_driver_congr h]

 

def stoppedData (S : GDriver→ℝ≥0∞) (b : GDriver) : ℝ≥0×GDriver :=
  ((S b).toNNReal,pastDriver (S b).toNNReal b)

lemma stoppedData_raw_measurable {S : GDriver→ℝ≥0∞}
    (hS : IsStoppingTime rawFiltration S) :
    Measurable[hS.measurableSpace] (stoppedData S) :=
  (ENNReal.measurable_toNNReal.comp hS.measurable).prodMk
    (pastDriver_stopping_measurable S hS)

lemma inverseUpper_stoppedData (a : ℝ) (ha : 0<a) (S : GDriver→ℝ≥0∞)
    (b : GDriver) : inverseUpper a ha (stoppedData S b).2 (stoppedData S b).1=
      inverseUpper a ha b (S b).toNNReal :=
  inverseUpper_driver_congr a ha (pastDriver_eq _ b)

lemma restartWeight_stoppedData (a : ℝ) (ha : 0<a) (S : GDriver→ℝ≥0∞)
    (b : GDriver) : restartWeight a (stoppedData S b).2 (stoppedData S b).1=
      restartWeight a b (S b).toNNReal :=
  restartWeight_driver_congr a ha (pastDriver_eq _ b)

lemma inverseUpper_stopped_raw_joint (a : ℝ) (ha : 1/4<a)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) :
    @Measurable (GDriver×UpperPlane) UpperPlane
      (hS.measurableSpace.prod inferInstance) inferInstance
      (fun p => inverseUpper a (lt_trans (by norm_num) ha) p.1 (S p.1).toNNReal p.2) := by
  have hD := stoppedData_raw_measurable hS
  have hin : @Measurable (GDriver×UpperPlane) (ℝ≥0×(GDriver×UpperPlane))
      (hS.measurableSpace.prod inferInstance) inferInstance (fun p =>
      ((stoppedData S p.1).1,((stoppedData S p.1).2,p.2))) :=
    (hD.fst.comp measurable_fst).prodMk ((hD.snd.comp measurable_fst).prodMk measurable_snd)
  have hh := (inverseUpper_joint_measurable a ha).comp hin
  simpa only [Function.comp_def,inverseUpper_stoppedData] using hh

lemma restartWeight_stopped_raw_joint (a : ℝ) (ha : 1/4<a)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) :
    @Measurable (GDriver×UpperPlane) ℝ≥0∞
      (hS.measurableSpace.prod inferInstance) inferInstance
      (fun p => restartWeight a p.1 (S p.1).toNNReal p.2) := by
  have hD := stoppedData_raw_measurable hS
  have hin : @Measurable (GDriver×UpperPlane) (ℝ≥0×(GDriver×UpperPlane))
      (hS.measurableSpace.prod inferInstance) inferInstance (fun p =>
      ((stoppedData S p.1).1,((stoppedData S p.1).2,p.2))) :=
    (hD.fst.comp measurable_fst).prodMk ((hD.snd.comp measurable_fst).prodMk measurable_snd)
  have hh := (restartWeight_joint_measurable a ha).comp hin
  simpa only [Function.comp_def,restartWeight_stoppedData a (lt_trans (by norm_num) ha)] using hh

end SLEExactGauge.LoewnerRestart
end
end

end OAI
