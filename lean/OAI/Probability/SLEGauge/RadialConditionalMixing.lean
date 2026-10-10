import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.RecoveredInteriorRestart
import OAI.Probability.SLEGauge.RadialRestartRaw

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator CenteredMoments

lemma radialLaw_consistent_le (W : Measure GDriver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (σ ρ : ℝ) (hρ : 0<ρ) (hρσ : ρ≤σ) (hσ : σ≤z.im)
    (A : Set GDriver)
    (hA : MeasurableSet[(radialTime_stopping a (by linarith) z hz σ
      (hρ.trans_le hρσ) hσ).measurableSpace] A) :
    radialLaw W a z ρ A=radialLaw W a z σ A := by
  rcases hρσ.eq_or_lt with rfl|hρσ
  · rfl
  · obtain ⟨_,_,hS,he⟩ := finite_radial_laws_consistent W hW a ha z hz ρ σ hρ hρσ hσ
    exact he A hA

 

theorem finiteAngle_conditional_integral_bounds (W : Measure GDriver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (σ ρ : ℝ) (hρ : 0<ρ) (hρσ : ρ≤σ) (hσ : σ≤z.im)
    (s : ℝ) (hs : Jacobi.mixingTime (4*a) ≤ s) (hgap : ρ=σ*Real.exp (-2*a*s))
    (A : Set GDriver)
    (hA : MeasurableSet[(radialTime_stopping a (by linarith) z hz σ
      (hρ.trans_le hρσ) hσ).measurableSpace] A)
    (f : Angle→ℝ≥0∞) (hf : Measurable f) :
    (1/2:ℝ≥0∞)*(∫⁻θ,f θ∂angleLaw a)*radialLaw W a z σ A ≤
      ∫⁻b in A,f (Jacobi.finiteAngle a z ρ b)∂radialLaw W a z ρ ∧
    (∫⁻b in A,f (Jacobi.finiteAngle a z ρ b)∂radialLaw W a z ρ) ≤
      2*(∫⁻θ,f θ∂angleLaw a)*radialLaw W a z σ A := by
  have hs0 : 0 ≤ s := le_trans (by unfold Jacobi.mixingTime Jacobi.majorantBase; positivity) hs
  have hσ0 := hρ.trans_le hρσ
  have he (w : UpperPlane) : w.1.im*(ρ/σ)=levelRadius a (2*w.1.im) s := by
    rw [hgap]
    unfold levelRadius
    field_simp
  have hb (w : UpperPlane) := Jacobi.finiteAngleLaw_integral_bounds W hW a ha w.1 w.2 s hs f hf
  have hb' (w : UpperPlane) :
      (1/2:ℝ≥0∞)*(∫⁻θ,f θ∂angleLaw a) ≤
        ∫⁻c,f (Jacobi.finiteAngle a w.1 (w.1.im*(ρ/σ)) c)∂radialLaw W a w.1 (w.1.im*(ρ/σ)) ∧
      (∫⁻c,f (Jacobi.finiteAngle a w.1 (w.1.im*(ρ/σ)) c)∂radialLaw W a w.1 (w.1.im*(ρ/σ))) ≤
        2*(∫⁻θ,f θ∂angleLaw a) := by
    rw [he w]
    simpa only [Jacobi.finiteAngleLaw,lintegral_map hf
      (Jacobi.finiteAngle_measurable a (by linarith) w.1 w.2 _
        (levelRadius_pos a _ s (mul_pos (by norm_num) w.2))
        (Jacobi.levelRadius_initial_le a (by linarith) w.1 w.2 s hs0))] using hb w
  rw [finiteAngle_conditional W hW a ha z hz σ ρ hρ hρσ hσ A hA f hf]
  constructor
  · simpa only [lintegral_const,Measure.restrict_apply_univ] using
      lintegral_mono (μ := (radialLaw W a z σ).restrict A)
        (fun b => (hb' (radialPoint a z σ b)).1)
  · simpa only [lintegral_const,Measure.restrict_apply_univ] using
      lintegral_mono (μ := (radialLaw W a z σ).restrict A)
        (fun b => (hb' (radialPoint a z σ b)).2)

 

theorem finiteAngle_conditional_bounds (W : Measure GDriver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (σ ρ : ℝ) (hρ : 0<ρ) (hρσ : ρ≤σ) (hσ : σ≤z.im)
    (s : ℝ) (hs : Jacobi.mixingTime (4*a) ≤ s) (hgap : ρ=σ*Real.exp (-2*a*s))
    (A : Set GDriver)
    (hA : MeasurableSet[(radialTime_stopping a (by linarith) z hz σ
      (hρ.trans_le hρσ) hσ).measurableSpace] A)
    (f : Angle→ℝ≥0∞) (hf : Measurable f) :
    (1/2:ℝ≥0∞)*(∫⁻θ,f θ∂angleLaw a)*radialLaw W a z ρ A ≤
      ∫⁻b in A,f (Jacobi.finiteAngle a z ρ b)∂radialLaw W a z ρ ∧
    (∫⁻b in A,f (Jacobi.finiteAngle a z ρ b)∂radialLaw W a z ρ) ≤
      2*(∫⁻θ,f θ∂angleLaw a)*radialLaw W a z ρ A := by
  rw [radialLaw_consistent_le W hW a ha z hz σ ρ hρ hρσ hσ A hA]
  exact finiteAngle_conditional_integral_bounds W hW a ha z hz σ ρ hρ hρσ hσ s hs hgap A hA f hf

 

lemma radial_change_law_event (W : Measure GDriver)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (ρ : ℝ) (hρ : 0<ρ) (hr : ρ≤z.im) (A : Set GDriver) (hA : MeasurableSet A) :
    W (A∩{b | radialTime a b.1 z ρ≠∞}) =
      ENNReal.ofReal (ρ^(alpha a)*physicalGreen a (z,0))*
        ∫⁻b in A,ENNReal.ofReal ((Real.sin (Jacobi.finiteAngle a z ρ b : ℝ))^(-p a))
          ∂radialLaw W a z ρ := by
  have he := Jacobi.radial_change_law W a ha z hz ρ hρ hr (A.indicator (fun _=>1))
    (measurable_const.indicator hA)
  have hi : (fun b => ENNReal.ofReal
      ((Real.sin (Jacobi.finiteAngle a z ρ b : ℝ))^(-p a))*A.indicator (fun _=>1) b) =
      A.indicator (fun b => ENNReal.ofReal
        ((Real.sin (Jacobi.finiteAngle a z ρ b : ℝ))^(-p a))) := by
    funext b
    by_cases hb : b∈A <;> simp [hb]
  simp only [hi,lintegral_indicator hA,Measure.restrict_restrict hA,lintegral_one,
    Measure.restrict_apply_univ] at he
  simpa only [inter_comm] using he

 

theorem radial_change_law_past_bound (W : Measure GDriver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (σ ρ : ℝ) (hρ : 0<ρ) (hρσ : ρ≤σ) (hσ : σ≤z.im)
    (s : ℝ) (hs : Jacobi.mixingTime (4*a) ≤ s) (hgap : ρ=σ*Real.exp (-2*a*s))
    (A : Set GDriver)
    (hA : MeasurableSet[(radialTime_stopping a (by linarith) z hz σ
      (hρ.trans_le hρσ) hσ).measurableSpace] A) :
    W (A∩{b | radialTime a b.1 z ρ≠∞}) ≤
      Jacobi.visitConstant a*ENNReal.ofReal ((ρ/z.im)^(alpha a))*radialLaw W a z ρ A := by
  have hA' : MeasurableSet A := (radialTime_stopping a (by linarith) z hz σ
    (hρ.trans_le hρσ) hσ).measurableSpace_le _ hA
  rw [radial_change_law_event W a ha z hz ρ hρ (hρσ.trans hσ) A hA']
  have hb := (finiteAngle_conditional_bounds W hW a ha z hz σ ρ hρ hρσ hσ s hs hgap A hA
    (fun θ=>ENNReal.ofReal ((Real.sin θ)^(-p a))) (by fun_prop)).2
  have hG : ENNReal.ofReal (ρ^(alpha a)*physicalGreen a (z,0)) ≤
      ENNReal.ofReal ((ρ/z.im)^(alpha a)) := by
    apply ENNReal.ofReal_le_ofReal
    rw [Real.div_rpow hρ.le hz.le,div_eq_mul_inv,←Real.rpow_neg hz.le]
    exact mul_le_mul_of_nonneg_left (Jacobi.physicalGreen_initial_bound a ha z hz)
      (Real.rpow_nonneg hρ.le _)
  calc
    _ ≤ ENNReal.ofReal ((ρ/z.im)^(alpha a))*
        (2*(∫⁻θ : Angle,ENNReal.ofReal ((Real.sin θ)^(-p a))∂angleLaw a)*radialLaw W a z ρ A) :=
      mul_le_mul hG hb zero_le zero_le
    _ ≤ _ := by
      rw [←mul_assoc,mul_comm (ENNReal.ofReal _) (2*_)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_right le_rfl) zero_le) zero_le

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions

lemma actualUpperMass_eval_joint_measurable (a : ℝ) (ha : 1/4<a) (q : ℝ)
    (hq : 0<q) (hq1 : q≤1) (f : C_c(UpperPlane,ℝ)) :
    Measurable (fun p : ℝ≥0∞×ExactSLEGenerator.Driver=>∫z,f z∂actualUpperMass a q p.1 p.2) := by
  simp_rw [actualUpperMass_eval a ha q hq hq1]
  have hm : Measurable (fun p : (ℝ≥0∞×ExactSLEGenerator.Driver) × ℂ =>
      upperExtension f p.2*(timeMassDensity a q p.1.1 p.1.2 p.2).toReal) :=
    ((upperExtension_measurable f).comp measurable_snd).mul
      (timeMassDensity_joint_measurable a ha q hq hq1).ennreal_toReal
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma recoveredMass_joint_measurable (a : ℝ) (ha : 1/4<a)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j) :
    Measurable (fun p : ℝ≥0∞×ExactSLEGenerator.Driver=>recoveredMass a ha s c hc p.1 p.2) := by
  apply measurable_radonLimit
  intro k f
  simp_rw [actualMassFunctionals_apply]
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.mul (actualUpperMass_eval_joint_measurable a ha _
    (Real.exp_pos _) (level_step_le_one a ha j) f)

lemma centeredTime_measurable (a : ℝ) (ha : 1/4<a) (l : ℕ) :
    Measurable (fun p : Angle×ExactSLEGenerator.Driver=>levelTime a p.1.1 p.2.1 l) := by
  have hz : Measurable (fun θ : Angle => (⟨fromDisk θ.1 0,by
      rw [fromDisk_zero_im]
      exact Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2⟩ : UpperPlane)) := by
    apply Measurable.subtype_mk
    simp only [fromDisk_zero]
    fun_prop
  have hr : Real.exp (-2*a*l)≤1 := Real.exp_le_one_iff.mpr (by
    have hl : (0:ℝ)≤l := Nat.cast_nonneg _
    have ha0 : 0<a := by linarith
    nlinarith)
  convert (joint_radialTime_measurable a ha _ (Real.exp_pos _) hr).comp
    (measurable_snd.prodMk (hz.comp measurable_fst)) using 1
  funext p
  simp only [levelTime_radialTime a p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.1.continuous,
    Function.comp_apply,fromDisk_zero_im]

lemma centeredWeight_measurable (a : ℝ) (ha : 1/4<a) (l : ℕ) :
    Measurable (fun p : Angle×ExactSLEGenerator.Driver=>tiltWeight a p.1.1 p.2.1 l) := by
  have hz : Measurable (fun θ : Angle => (⟨fromDisk θ.1 0,by
      rw [fromDisk_zero_im]
      exact Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2⟩ : UpperPlane)) := by
    apply Measurable.subtype_mk
    simp only [fromDisk_zero]
    fun_prop
  have hr : Real.exp (-2*a*l)≤1 := Real.exp_le_one_iff.mpr (by
    have hl : (0:ℝ)≤l := Nat.cast_nonneg _
    have ha0 : 0<a := by linarith
    nlinarith)
  have hG : Measurable (fun θ : Angle=>physicalGreen a (fromDisk θ.1 0,0)) := by
    have he : (fun θ : Angle=>physicalGreen a (fromDisk θ.1 0,0))=
        fun θ : Angle => Real.sin θ.1^(-alpha a)*Real.sin θ.1^(p a) := by
      funext θ
      exact radial_initial_green a θ.1 θ.2.1 θ.2.2
    rw [he]
    fun_prop
  convert ((joint_radialWeight_measurable a ha _ (Real.exp_pos _) hr).comp
    (measurable_snd.prodMk (hz.comp measurable_fst))).div (hG.comp measurable_fst) using 1
  funext p
  simp only [tiltWeight_radialWeight a p.1.1 ha p.1.2.1 p.1.2.2 p.2 l,Function.comp_apply,Pi.div_apply,fromDisk_zero_im]

lemma diskMap_joint_measurable :
    Measurable (fun p : Angle×UpperPlane => diskMap p.1.1 p.2.1) := by
  unfold diskMap
  fun_prop

lemma diskWeight_joint_measurable (a : ℝ) :
    Measurable (fun p : Angle×UpperPlane => diskWeight a p.1.1 p.2) := by
  have he : (fun p : Angle×UpperPlane=>diskWeight a p.1.1 p.2)=
      fun p : Angle×UpperPlane =>
        ‖((2*Real.sin p.1.1:ℝ):ℂ)*Complex.I/(p.2.1-Complex.exp (-Complex.I*p.1.1))^2‖^(2-alpha a) := by
    funext p
    rw [diskWeight,disk_deriv p.1.1 p.1.2.1 p.1.2.2 p.2]
  rw [he]
  fun_prop

 

lemma diskMass_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    (a : ℝ) (θ : Ω→Angle) (hθ : Measurable θ) (ν : Ω→Measure UpperPlane)
    (hν : Measurable ν) [∀ω,IsFiniteMeasureOnCompacts (ν ω)] :
    Measurable (fun ω=>diskMass a (θ ω).1 (ν ω)) := by
  let k : Kernel Ω UpperPlane := ⟨ν,hν⟩
  have : IsSFiniteKernel k := isSFiniteKernel_of_locally_finite k
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hm : Measurable (fun p : Ω×UpperPlane =>
      A.indicator (fun _=> (1:ℝ≥0∞)) (diskMap (θ p.1).1 p.2.1)*
        ENNReal.ofReal (diskWeight a (θ p.1).1 p.2)) :=
    ((measurable_const.indicator hA).comp (diskMap_joint_measurable.comp
      ((hθ.comp measurable_fst).prodMk measurable_snd))).mul
      ((diskWeight_joint_measurable a).comp
        ((hθ.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal
  have he (ω : Ω) : diskMass a (θ ω).1 (ν ω) A =
      ∫⁻z,A.indicator (fun _=>(1:ℝ≥0∞)) (diskMap (θ ω).1 z.1)*
        ENNReal.ofReal (diskWeight a (θ ω).1 z)∂k ω := by
    rw [diskMass,Measure.map_apply (diskMap_measurable _) hA,
      withDensity_apply _ ((diskMap_measurable _) hA),
      ←lintegral_indicator ((diskMap_measurable _) hA)]
    apply lintegral_congr
    intro z
    by_cases hz : diskMap (θ ω).1 z.1∈A <;>
      simp [Set.indicator,Set.mem_preimage,hz]
  simp_rw [he]
  exact hm.lintegral_kernel_prod_right

 

def centeredMass (a : ℝ) (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    (l : ℕ) (p : Angle×ExactSLEGenerator.Driver) : ℝ≥0∞ :=
  diskMass a p.1.1 (μ (levelTime a p.1.1 p.2.1 l) p.2) (Metric.closedBall (0:ℂ) (1/4))

lemma centeredMass_measurable (a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    (hμ : Measurable (fun p : ℝ≥0∞×ExactSLEGenerator.Driver=>μ p.1 p.2))
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)] (l : ℕ) :
    Measurable (centeredMass a μ l) := by
  have hn := diskMass_joint_measurable a Prod.fst measurable_fst
    (fun p : Angle×ExactSLEGenerator.Driver=>μ (levelTime a p.1.1 p.2.1 l) p.2)
    (hμ.comp ((centeredTime_measurable a ha l).prodMk measurable_snd))
  exact (Measure.measurable_coe (Metric.isClosed_closedBall).measurableSet).comp hn

end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions

 

def finiteAngleLaw (W : Measure ExactSLEGenerator.Driver) (a : ℝ) (l : ℕ) :
    Measure (Angle×ExactSLEGenerator.Driver) :=
  ((angleLaw a).prod W).withDensity (fun p=>ENNReal.ofReal (tiltWeight a p.1.1 p.2.1 l))

lemma finiteAngleLaw_absolutelyContinuous (W : Measure ExactSLEGenerator.Driver)
    (a : ℝ) (l : ℕ) : finiteAngleLaw W a l≪(angleLaw a).prod W :=
  withDensity_absolutelyContinuous _ _

lemma finiteAngleLaw_lintegral (W : Measure ExactSLEGenerator.Driver) [SFinite W]
    (a : ℝ) (ha : 1/4<a) (l : ℕ)
    (f : Angle×ExactSLEGenerator.Driver→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻p,f p∂finiteAngleLaw W a l)=∫⁻θ : Angle,∫⁻b,f (θ,b)
      ∂radialLaw W a (fromDisk θ.1 0) (Real.sin θ.1*Real.exp (-2*a*l))∂angleLaw a := by
  have hD := (centeredWeight_measurable a ha l).ennreal_ofReal
  rw [finiteAngleLaw,lintegral_withDensity_eq_lintegral_mul _ hD hf,
    lintegral_prod _ ((hD.mul hf).aemeasurable)]
  apply lintegral_congr
  intro θ
  have hd := hD.comp ((measurable_const (a:=θ)).prodMk measurable_id)
  have ht := hf.comp ((measurable_const (a:=θ)).prodMk measurable_id)
  have he : (fun b : ExactSLEGenerator.Driver=>ENNReal.ofReal (tiltWeight a θ.1 b.1 l))=
      fun b : ExactSLEGenerator.Driver=>ENNReal.ofReal (radialWeight a b.1 (fromDisk θ.1 0)
        (Real.sin θ.1*Real.exp (-2*a*l))/physicalGreen a (fromDisk θ.1 0,0)) := by
    funext b
    rw [tiltWeight_radialWeight a θ.1 ha θ.2.1 θ.2.2 b l]
  change (∫⁻b,ENNReal.ofReal (tiltWeight a θ.1 b.1 l)*f (θ,b)∂W)=_
  rw [radialLaw,←he]
  exact (lintegral_withDensity_eq_lintegral_mul W hd ht).symm

lemma finiteAngleLaw_probability (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver)=>b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (l : ℕ) : IsProbabilityMeasure (finiteAngleLaw W a l) := by
  have ha0 : 0<a := by linarith
  have : IsProbabilityMeasure (angleLaw a) := angleLaw_probability a ha0.le
  have hp (θ : Angle) : IsProbabilityMeasure
      (radialLaw W a (fromDisk θ.1 0) (Real.sin θ.1*Real.exp (-2*a*l))) := by
    have hs := Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2
    apply radialLaw_probability W hW a ha _ (by simpa only [fromDisk_zero_im] using hs)
    · exact mul_pos hs (Real.exp_pos _)
    · rw [fromDisk_zero_im]
      apply mul_le_of_le_one_right hs.le
      apply Real.exp_le_one_iff.mpr
      have hl : (0:ℝ)≤l := Nat.cast_nonneg _
      nlinarith
  have (θ : Angle) : IsProbabilityMeasure
      (radialLaw W a (fromDisk θ.1 0) (Real.sin θ.1*Real.exp (-2*a*l))) := hp θ
  rw [isProbabilityMeasure_iff,←lintegral_one,
    finiteAngleLaw_lintegral W a ha l _ measurable_const]
  simp only [lintegral_one, measure_univ]

 

def finiteMoment (W : Measure ExactSLEGenerator.Driver) (a : ℝ)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane) (m l : ℕ) : ℝ≥0∞ :=
  ∫⁻p,(centeredMass a μ l p)^m∂finiteAngleLaw W a l

 

theorem common_limit_mixed_moment_bound (a : ℝ) (ha : 1/4<a)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃D : ℝ≥0∞,D<∞ ∧ ∀(W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
      IsBrownianReal (fun t (b : ExactSLEGenerator.Driver)=>b.1 t) W →
      ∀(s : ℕ→Finset ℕ) (coeff : ℕ→ℕ→ℝ),
      (∀k j,j∈s k→0≤coeff k j) → (∀k,∑j∈s k,coeff k j=1) →
      ∀μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane,
      (∀v b,IsFiniteMeasureOnCompacts (μ v b)) →
      Measurable (fun p : ℝ≥0∞×ExactSLEGenerator.Driver=>μ p.1 p.2) →
      (∀ᵐ b∂W,∀v : ℝ≥0∞,μ v b≤μ ∞ b) →
      (∀ᵐ b∂W,∀f : C_c(UpperPlane,ℝ),Tendsto (fun k=>∑j∈s k,coeff k j*
        ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) ∞ b)
          atTop (𝓝 (∫z,f z∂μ ∞ b))) →
      ∀l, finiteMoment W a μ m l≤D := by
  obtain ⟨C,hC,hCb⟩ := common_limit_disk_tilted_moment a ha m hm
  let J := ∫⁻θ : Angle,ENNReal.ofReal (Real.sin θ.1^(-p a))∂angleLaw a
  refine ⟨C*J,ENNReal.mul_lt_top hC (angle_inverse_power_finite a),?_⟩
  intro W hprob hW s coeff hcoeff hsum μ hμfin hμ hmono hlim l
  let (v : ℝ≥0∞) (b : ExactSLEGenerator.Driver) : IsFiniteMeasureOnCompacts (μ v b) := hμfin v b
  rw [finiteMoment,finiteAngleLaw_lintegral W a ha l _
    ((centeredMass_measurable a ha μ hμ l).pow_const m)]
  calc
    _ ≤ ∫⁻θ : Angle,C*ENNReal.ofReal (Real.sin θ.1^(-p a))∂angleLaw a := by
      apply lintegral_mono
      intro θ
      let T := fun b : ExactSLEGenerator.Driver=>levelTime a θ.1 b.1 l
      exact hCb W hW s coeff hcoeff hsum μ (hμfin ∞)
        (hμ.comp (measurable_const.prodMk measurable_id)) hmono hlim
        θ.1 θ.2.1 θ.2.2 l T
    _ = C*J := lintegral_const_mul _ (by fun_prop)

end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator CenteredMoments LoewnerScaling

 
def pointAngle (w : UpperPlane) : Angle := Jacobi.angleState (w.1,0)

lemma pointAngle_measurable : Measurable pointAngle :=
  Jacobi.angleState_measurable.comp (measurable_subtype_coe.prodMk measurable_const)

lemma point_norm_pos (w : UpperPlane) : 0<‖w.1‖ := w.2.trans_le (Complex.im_le_norm _)

lemma fromDisk_pointAngle (w : UpperPlane) :
    fromDisk (pointAngle w).1 0 = ((‖w.1‖:ℝ):ℂ)⁻¹*w.1 := by
  have hn := point_norm_pos w
  have hs := Jacobi.sin_physicalTheta (w.1,0) w.2
  have hc := physicalTheta_cot (w.1,0)
  have hsin := Real.sin_pos_of_pos_of_lt_pi (pointAngle w).2.1 (pointAngle w).2.2
  change Real.sin (pointAngle w).1 = w.1.im/‖w.1‖ at hs
  change Real.cot (pointAngle w).1 = w.1.re/w.1.im at hc
  rw [Real.cot_eq_cos_div_sin,hs,div_eq_div_iff (div_ne_zero w.2.ne' hn.ne') w.2.ne'] at hc
  have hcos : Real.cos (pointAngle w).1=w.1.re/‖w.1‖ := by
    apply (eq_div_iff hn.ne').mpr
    field_simp at hc
    exact (mul_left_cancel₀ w.2.ne' (by nlinarith :
      w.1.im * (Real.cos (pointAngle w).1 * ‖w.1‖) = w.1.im * w.1.re))
  rw [fromDisk_zero,mul_comm,Complex.exp_mul_I,←Complex.ofReal_inv]
  simp only [←Complex.ofReal_cos, ←Complex.ofReal_sin]
  apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
    add_zero,zero_add,mul_one,sub_zero]
  · rw [hcos]; ring
  · rw [hs]; ring

lemma norm_mul_fromDisk_pointAngle (w : UpperPlane) :
    ((‖w.1‖:ℝ):ℂ)*fromDisk (pointAngle w).1 0=w.1 := by
  rw [fromDisk_pointAngle,←mul_assoc,mul_inv_cancel₀
    (Complex.ofReal_ne_zero.mpr (point_norm_pos w).ne'),one_mul]

lemma sin_pointAngle (w : UpperPlane) : Real.sin (pointAngle w).1=w.1.im/‖w.1‖ :=
  Jacobi.sin_physicalTheta (w.1,0) w.2

 
def normalizeDriver (w : UpperPlane) (b : GDriver) : GDriver :=
  scaleDriver ‖w.1‖₊ b

lemma continuous_normalizeDriver : Continuous (fun p : UpperPlane×GDriver => normalizeDriver p.1 p.2) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (UpperPlane×GDriver)×ℝ≥0 =>
    ‖p.1.1.1‖⁻¹*p.1.2.1 (‖p.1.1.1‖₊^2*p.2))
  have hn : Continuous (fun p : (UpperPlane×GDriver)×ℝ≥0 => ‖p.1.1.1‖) := by fun_prop
  have ht : Continuous (fun p : (UpperPlane×GDriver)×ℝ≥0 =>
      ‖p.1.1.1‖₊^2*p.2) := by
    exact ((hn.pow 2).mul (NNReal.continuous_coe.comp continuous_snd)).subtype_mk _
  exact (hn.inv₀ (fun p=>(point_norm_pos p.1.1).ne')).mul
    (continuous_eval.comp ((continuous_subtype_val.comp continuous_fst.snd).prodMk
      ht))

lemma radiusDensity_scaled (a : ℝ) (ha : 0<a) {c : ℝ≥0} (hc : 0<c)
    (b : GDriver) (z : ℂ) (hz : 0<z.im) (ρ : ℝ) (hρ : 0<ρ) (hr : ρ≤z.im) :
    radiusDensity a z ρ (scaleDriver c b)=
      radiusDensity a (((c:ℝ):ℂ)*z) ((c:ℝ)*ρ) b := by
  have he : (z,(0:ℝ))=scaleState c ((((c:ℝ):ℂ)*z),0) := by
    simp only [scaleState,←mul_assoc,inv_mul_cancel₀
      (Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr hc).ne'),one_mul]
  have hy : 0<Y ((((c:ℝ):ℂ)*z),0) := by
    simpa [Complex.mul_im] using mul_pos (show 0<(c:ℝ) from hc) hz
  unfold radiusDensity
  rw [radialWeight_scaled a ha hc b z hz ρ hρ hr,he,scaleState_green a hc _ hy,
    mul_div_mul_left _ _ (Real.rpow_pos_of_pos (show 0<(c:ℝ) from hc) (alpha a)).ne']

 

lemma radialLaw_scale_integral (W : Measure GDriver)
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) {c : ℝ≥0} (hc : 0<c)
    (z : ℂ) (hz : 0<z.im) (ρ : ℝ) (hρ : 0<ρ) (hr : ρ≤z.im)
    (f : GDriver→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻b,f (scaleDriver c b)∂radialLaw W a (((c:ℝ):ℂ)*z) ((c:ℝ)*ρ))=
      ∫⁻b,f b∂radialLaw W a z ρ := by
  have hz' : 0<(((c:ℝ):ℂ)*z).im := by
    simpa [Complex.mul_im] using mul_pos (show 0<(c:ℝ) from hc) hz
  have hρ' : 0<(c:ℝ)*ρ := mul_pos hc hρ
  have hr' : (c:ℝ)*ρ≤(((c:ℝ):ℂ)*z).im := by
    simpa [Complex.mul_im] using mul_le_mul_of_nonneg_left hr c.coe_nonneg
  change (∫⁻b,f (scaleDriver c b)∂W.withDensity (radiusDensity a (((c:ℝ):ℂ)*z) ((c:ℝ)*ρ)))=
    ∫⁻b,f b∂W.withDensity (radiusDensity a z ρ)
  have hleft := lintegral_withDensity_eq_lintegral_mul W
    (radiusDensity_measurable a ha _ hz' _ hρ' hr') (hf.comp (continuous_scaleDriver c).measurable)
  simp only [Function.comp_def] at hleft
  rw [hleft, lintegral_withDensity_eq_lintegral_mul W (radiusDensity_measurable a ha z hz ρ hρ hr) hf]
  simp only [Pi.mul_apply]
  simp_rw [←radiusDensity_scaled a (by linarith) hc _ z hz ρ hρ hr]
  exact (measurePreserving_scaleDriver hW hc).lintegral_comp
    ((radiusDensity_measurable a ha z hz ρ hρ hr).mul hf)

end SLEExactGauge.LoewnerRestart
end
end

end OAI
