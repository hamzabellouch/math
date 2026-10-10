import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.NormalizedRadialTests

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions CompactSequence

lemma centeredMass_raw_measurable_of_le (a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)] (θ : Angle) {i l : ℕ} (hil : i≤l)
    (hμ : Measurable[(centeredTime_stopping a ha θ i).measurableSpace]
      (fun b=>μ (levelTime a θ.1 b.1 i) b)) :
    Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
      (fun b=>centeredMass a μ i (θ,b)) :=
  (centeredMass_raw_measurable a ha μ θ i hμ).mono
    ((centeredTime_stopping a ha θ i).measurableSpace_mono (centeredTime_stopping a ha θ l)
      (fun b=>centeredTime_monotone a ha θ b hil)) le_rfl

lemma centered_vector_consistent (W : Measure ExactSLEGenerator.Driver)
    [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver)=>b.1 t) W)
    (a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    (hμ : Measurable (fun p : ℝ≥0∞×ExactSLEGenerator.Driver=>μ p.1 p.2))
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)]
    (hμraw : ∀l θ,Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
      (fun b=>μ (levelTime a θ.1 b.1 l) b))
    {l k : ℕ} (hlk : l≤k) :
    (finiteAngleLaw W a k).map (fun p=>fun i : Fin (l+1)=>centeredMass a μ i p)=
      (finiteAngleLaw W a l).map (fun p=>fun i : Fin (l+1)=>centeredMass a μ i p) := by
  have hm : Measurable (fun p=>fun i : Fin (l+1)=>centeredMass a μ i p) :=
    Measurable.of_eval (fun index=>centeredMass_measurable a ha μ hμ index)
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hm hA,Measure.map_apply hm hA]
  simp only [←lintegral_indicator_one (hm hA)]
  apply finiteAngleLaw_lintegral_consistent W hW a ha hlk
  · exact measurable_const.indicator (hm hA)
  · intro θ
    let : MeasurableSpace ExactSLEGenerator.Driver := (centeredTime_stopping a ha θ l).measurableSpace
    have hv : Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
        (fun b=>fun i : Fin (l+1)=>centeredMass a μ i (θ,b)) :=
      Measurable.of_eval (fun index=>centeredMass_raw_measurable_of_le a ha μ θ
        (by omega) (hμraw index θ))
    exact measurable_const.indicator (hv hA)

 

theorem exists_centered_sequence_law (W : Measure ExactSLEGenerator.Driver)
    [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver)=>b.1 t) W)
    (a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    (hμ : Measurable (fun p : ℝ≥0∞×ExactSLEGenerator.Driver=>μ p.1 p.2))
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)]
    (hμraw : ∀l θ,Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
      (fun b=>μ (levelTime a θ.1 b.1 l) b))
    (hmono : ∀ᵐ b∂W,Monotone (fun v=>μ v b)) :
    ∃Q : Measure (ℕ→ℝ≥0∞),IsProbabilityMeasure Q ∧
      (∀n,Q.map (initialVector n)=(finiteAngleLaw W a n).map
        (fun p=>fun i : Fin (n+1)=>centeredMass a μ i p)) ∧
      (∀ᵐ x∂Q,Monotone x) := by
  have (n : ℕ) : IsProbabilityMeasure (finiteAngleLaw W a n) :=
    finiteAngleLaw_probability W hW a ha n
  obtain ⟨Q,hQ,hQlaw⟩ := exists_sequence_law (finiteAngleLaw W a)
    (centeredMass a μ) (centeredMass_measurable a ha μ hμ)
    (fun _ _ hlk=>centered_vector_consistent W hW a ha μ hμ hμraw hlk)
  refine ⟨Q,hQ,hQlaw,?_⟩
  have hX (l : ℕ) : ∀ᵐ p∂finiteAngleLaw W a l,Monotone (fun n=>centeredMass a μ n p) := by
    have hb : ∀ᵐ p ∂(angleLaw a).prod W,Monotone (fun v=>μ v p.2) :=
      Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hmono
    filter_upwards [(finiteAngleLaw_absolutelyContinuous W a l).ae_le hb] with p hp
    exact centeredMass_monotone a ha μ p.2 hp p.1
  have hs (n : ℕ) : ∀ᵐ x∂Q,x n≤x (n+1) := by
    let i : Fin (n+1+1) := ⟨n,by omega⟩
    let j : Fin (n+1+1) := ⟨n+1,by omega⟩
    have hm : MeasurableSet {x : Fin (n+1+1)→ℝ≥0∞ | x i≤x j} :=
      measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _)
    change ∀ᵐ x∂Q,(initialVector (n+1) x) i≤(initialVector (n+1) x) j
    rw [←ae_map_iff (measurable_initialVector (n+1)).aemeasurable hm,hQlaw]
    apply (ae_map_iff (Measurable.of_eval
      (fun index : Fin (n+1+1)=>centeredMass_measurable a ha μ hμ index)).aemeasurable hm).mpr
    filter_upwards [hX (n+1)] with p hp
    exact hp (by simp only [i,j]; omega)
  filter_upwards [ae_all_iff.mpr hs] with x hx
  exact monotone_nat_of_le_succ hx

 

def diskSequenceMass (x : ℕ→ℝ≥0∞) : ℝ≥0∞ := ⨆n,x n

lemma diskSequenceMass_measurable : Measurable diskSequenceMass :=
  Measurable.iSup (fun _=>measurable_pi_apply _)

lemma diskSequenceMass_tendsto {x : ℕ→ℝ≥0∞} (hx : Monotone x) :
    Tendsto x atTop (𝓝 (diskSequenceMass x)) := tendsto_atTop_iSup hx

 

theorem diskSequence_moment (W : Measure ExactSLEGenerator.Driver)
    (a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    (hμ : Measurable (fun p : ℝ≥0∞×ExactSLEGenerator.Driver=>μ p.1 p.2))
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)]
    (Q : Measure (ℕ→ℝ≥0∞))
    (hQlaw : ∀n,Q.map (initialVector n)=(finiteAngleLaw W a n).map
      (fun p=>fun i : Fin (n+1)=>centeredMass a μ i p))
    (hQmono : ∀ᵐ x∂Q,Monotone x) (m : ℕ) :
    (∫⁻x,(diskSequenceMass x)^m∂Q)=⨆l,finiteMoment W a μ m l := by
  simp only [diskSequenceMass,ENNReal.iSup_pow]
  rw [lintegral_iSup' (fun _=>(measurable_pi_apply _).pow_const m |>.aemeasurable)
    (hQmono.mono (fun _ hx _ _ hij=>pow_le_pow_left' (hx hij) m))]
  congr with l
  exact lintegral_coordinate Q (finiteAngleLaw W a l) (centeredMass a μ)
    (centeredMass_measurable a ha μ hμ) l (hQlaw l) (fun x=>x^m)
    (measurable_id.pow_const m)

end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions
open TraceMassIntegration TraceMassContinuity CompactSequence

 

theorem actual_centered_finite_moments (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure TDriver) (hW : Target.IsWiener W) :
    ∃ (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j),
      (∀k j,j∈s k→k≤j) ∧ (∀k,∑j∈s k,c k j=1) ∧
      let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
      (∀v b,IsFiniteMeasureOnCompacts (μ v b) ∧ (μ v b).Regular) ∧
      Measurable (fun p : ℝ≥0∞×GDriver=>μ p.1 p.2) ∧
      (∀(S : GDriver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S),
        Measurable[hS.measurableSpace] (fun b=>μ (S b) b)) ∧
      (∀ᵐ b∂W,TraceMassFacts κ b (fun v=>μ v (driverHomeomorph b)) ∧
        (∀v : ℝ≥0∞,∀f : C_c(UpperPlane,ℝ),Tendsto
          (fun k=>∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
             (Real.exp (-2*(Target.a κ)*(j+1))) v (driverHomeomorph b))
          atTop (𝓝 (∫z,f z∂μ v (driverHomeomorph b)))) ∧
        (∀u v : ℝ≥0,u<v →
          0<(μ v (driverHomeomorph b)-μ u (driverHomeomorph b)) univ)) ∧
      ∃Q : Measure (ℕ→ℝ≥0∞),IsProbabilityMeasure Q ∧
        (∀n,Q.map (initialVector n)=(finiteAngleLaw (W.map driverHomeomorph) (Target.a κ) n).map
          (fun p=>fun i : Fin (n+1)=>centeredMass (Target.a κ) μ i p)) ∧
        (∀ᵐ x∂Q,Monotone x ∧ Tendsto x atTop (𝓝 (diskSequenceMass x)) ∧ diskSequenceMass x<∞) ∧
        (∀ m : ℕ, 1 ≤ m →
          (∫⁻x,(diskSequenceMass x)^m∂Q)<∞ ∧
          (∫⁻x,(diskSequenceMass x)^m∂Q)=⨆l,finiteMoment (W.map driverHomeomorph) (Target.a κ) μ m l ∧
          Tendsto (finiteMoment (W.map driverHomeomorph) (Target.a κ) μ m) atTop
            (𝓝 (∫⁻x,(diskSequenceMass x)^m∂Q))) := by
  obtain ⟨s,c,hc,hs,hsum,hreg,hzero,hmeas,hprog,hmean,hstop,hpath⟩ :=
    actual_canonical_trace_mass κ hκ hκ8 W hW
  let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
  let V := W.map driverHomeomorph
  have hBW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) V := brownian_map_driver W hW
  have : IsProbabilityMeasure V := hBW.isGaussianProcess.isProbabilityMeasure
  have (v : ℝ≥0∞) (b : GDriver) : IsFiniteMeasureOnCompacts (μ v b) := (hreg v b).1
  have hμ : Measurable (fun p : ℝ≥0∞×GDriver=>μ p.1 p.2) :=
    recoveredMass_joint_measurable (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
  have hr (l : ℕ) (θ : Angle) :
      Measurable[(centeredTime_stopping (Target.a κ) (a_gt_quarter hκ hκ8) θ l).measurableSpace]
        (fun b=>μ (levelTime (Target.a κ) θ.1 b.1 l) b) := (hstop _ _).1
  have hp : ∀ᵐ b∂V,TraceMassFacts κ (driverHomeomorph.symm b) (fun v=>μ v b) := by
    apply driverMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hpath] with b hb
    change TraceMassFacts κ (driverHomeomorph.symm (driverHomeomorph b))
      (fun v=>μ v (driverHomeomorph b))
    simpa only [Homeomorph.symm_apply_apply] using hb.1
  have hv : ∀ᵐ b∂V,∀f : C_c(UpperPlane,ℝ),Tendsto
      (fun k=>∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
        (Real.exp (-2*(Target.a κ)*(j+1))) ∞ b) atTop (𝓝 (∫z,f z∂μ ∞ b)) := by
    apply driverMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
    exact hpath.mono (fun b hb=>hb.2.1 ∞)
  have hmono : ∀ᵐ b∂V,Monotone (fun v=>μ v b) := hp.mono (fun b hb=>hb.monotone)
  obtain ⟨Q,hQ,hlaw,hQmono⟩ := exists_centered_sequence_law V hBW (Target.a κ)
    (a_gt_quarter hκ hκ8) μ hμ hr hmono
  have he (m : ℕ) : (∫⁻x,(diskSequenceMass x)^m∂Q)=⨆l,finiteMoment V (Target.a κ) μ m l :=
    diskSequence_moment V (Target.a κ) (a_gt_quarter hκ hκ8) μ hμ Q hlaw hQmono m
  have hf (m : ℕ) (hm : 1 ≤ m) : (∫⁻x,(diskSequenceMass x)^m∂Q)<∞ := by
    obtain ⟨D,hD,hDb⟩ := common_limit_mixed_moment_bound (Target.a κ) (a_gt_quarter hκ hκ8) m hm
    rw [he]
    apply lt_of_le_of_lt (iSup_le (fun l=> ?_)) hD
    exact hDb V hBW s c hc hsum μ (fun v b=>(hreg v b).1) hμ
      (hmono.mono (fun b hb v=>hb le_top)) hv l
  have hfin : ∀ᵐ x∂Q,diskSequenceMass x<∞ := ae_lt_top (diskSequenceMass_measurable)
    (show (∫⁻x,diskSequenceMass x∂Q)≠∞ by simpa only [pow_one] using (hf 1 le_rfl).ne)
  refine ⟨s,c,hc,hs,hsum,hreg,hμ,fun S hS=>(hstop S hS).1,?_,Q,hQ,hlaw,?_,?_⟩
  · filter_upwards [hpath] with b hb
    exact ⟨hb.1,hb.2.1,fun u v huv=>(hb.2.2 u v huv).1⟩
  · filter_upwards [hQmono,hfin] with x hx hxf
    exact ⟨hx,diskSequenceMass_tendsto hx,hxf⟩
  · intro m hm
    refine ⟨hf m hm,he m,?_⟩
    rw [he]
    exact tendsto_atTop_iSup (finiteMoment_monotone V hBW (Target.a κ)
      (a_gt_quarter hκ hκ8) μ hμ hr hmono m)

end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions
open TraceMassIntegration TraceMassContinuity

lemma diskMap_norm_lt_one (θ : Angle) (z : UpperPlane) : ‖diskMap θ.1 z.1‖<1 := by
  let e := upperAffine (Real.cos θ.1) (Real.sin θ.1)
    (Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2)
  have he := diskMap_affine θ.1 θ.2.1 θ.2.2 (e.symm z).1
  rw [←upperAffine_apply,Homeomorph.apply_symm_apply] at he
  rw [he]
  have h := LiteralTrace.halfPlane_disk_norm_lt_one (e.symm z).2
    (show 0<Complex.I.im by norm_num)
  simpa only [map_mul,Complex.star_def,Complex.conj_I,sub_neg_eq_add] using h

lemma diskWeight_pos (a : ℝ) (θ : Angle) (z : UpperPlane) :
    0<diskWeight a θ.1 z := by
  apply Real.rpow_pos_of_pos
  apply norm_pos_iff.mpr
  rw [disk_deriv θ.1 θ.2.1 θ.2.2 z]
  apply div_ne_zero
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos (by norm_num)
      (Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2)).ne') Complex.I_ne_zero
  · exact pow_ne_zero _ (disk_denominator_ne θ.1 θ.2.1 θ.2.2 z)

lemma diskMass_unit_pos (a : ℝ) (θ : Angle) (ν : Measure UpperPlane)
    (hν : 0<ν univ) : 0<diskMass a θ.1 ν (Metric.ball (0:ℂ) 1) := by
  have he : (fun z : UpperPlane=>diskMap θ.1 z.1) ⁻¹' Metric.ball (0:ℂ) 1=univ := by
    ext z
    simp only [mem_preimage,Metric.mem_ball,dist_zero_right,mem_univ,iff_true]
    exact diskMap_norm_lt_one θ z
  rw [diskMass,Measure.map_apply (diskMap_measurable θ.1) Metric.isOpen_ball.measurableSet,
    he,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    lintegral_pos_iff_support ((diskWeight_measurable a θ.1 θ.2.1 θ.2.2).ennreal_ofReal)]
  have hs : Function.support (fun z : UpperPlane=>ENNReal.ofReal (diskWeight a θ.1 z))=univ := by
    ext z
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (ENNReal.ofReal_pos.mpr (diskWeight_pos a θ z)).ne'
  rw [hs]
  exact hν

 

def subdiskMass (a : ℝ) (μ : ℝ≥0∞→GDriver→Measure UpperPlane)
    (r : ℝ) (l : ℕ) (p : Angle×GDriver) : ℝ≥0∞ :=
  diskMass a p.1.1 (μ (levelTime a p.1.1 p.2.1 l) p.2) (Metric.closedBall (0:ℂ) r)

lemma subdiskMass_quarter (a : ℝ) (μ : ℝ≥0∞→GDriver→Measure UpperPlane) :
    subdiskMass a μ (1/4)=centeredMass a μ := rfl

lemma subdiskMass_measurable (a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→GDriver→Measure UpperPlane)
    (hμ : Measurable (fun p : ℝ≥0∞×GDriver=>μ p.1 p.2))
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)] (r : ℝ) (l : ℕ) :
    Measurable (subdiskMass a μ r l) := by
  exact (Measure.measurable_coe Metric.isClosed_closedBall.measurableSet).comp
    (diskMass_joint_measurable a Prod.fst measurable_fst
      (fun p : Angle×GDriver=>μ (levelTime a p.1.1 p.2.1 l) p.2)
      (hμ.comp ((centeredTime_measurable a ha l).prodMk measurable_snd)))

lemma centeredTime_pos (a : ℝ) (ha : 0<a) (θ : Angle) (b : GDriver)
    (l : ℕ) (hl : 0<l) : 0<levelTime a θ.1 b.1 l := by
  rw [levelTime_radialTime a θ.1 θ.2.1 θ.2.2 b.1 b.1.continuous]
  apply bot_lt_iff_ne_bot.mpr
  have hz : 0<(fromDisk θ.1 0).im := by
    rw [fromDisk_zero_im]
    exact Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2
  simpa only [ENNReal.bot_eq_zero,fromDisk_zero_im] using radialTime_ne_zero a ha (Real.exp (-2*a*l))
    (Real.exp_pos _) (Real.exp_lt_one_iff.mpr (by
      have hl' : (0:ℝ)<l := Nat.cast_pos.mpr hl
      nlinarith)) b (fromDisk θ.1 0) hz

 

def subdiskRadius (n : ℕ) : ℝ := 1-1/(n+2:ℝ)

lemma subdiskRadius_pos (n : ℕ) : 0<subdiskRadius n := by
  unfold subdiskRadius
  have hn : (1:ℝ)<n+2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hn0 : (0:ℝ)<n+2 := by positivity
  exact sub_pos.mpr ((div_lt_one hn0).mpr hn)

lemma subdiskRadius_lt_one (n : ℕ) : subdiskRadius n<1 := by
  unfold subdiskRadius
  have : (0:ℝ)<1/(n+2:ℝ) := by positivity
  linarith

lemma unitBall_eq_iUnion_subdisk : Metric.ball (0:ℂ) 1=
    ⋃n : ℕ,Metric.closedBall (0:ℂ) (subdiskRadius n) := by
  ext z
  simp only [Metric.mem_ball,Metric.mem_closedBall,dist_zero_right,mem_iUnion]
  constructor
  · intro hz
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hz)
    refine ⟨n,?_⟩
    have hle : (1:ℝ)/(n+2)≤1/(n+1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    dsimp [subdiskRadius]
    linarith
  · rintro ⟨n,hn⟩
    exact hn.trans_lt (subdiskRadius_lt_one n)

 

theorem exists_subdisk_positive_mean (W : Measure GDriver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (μ : ℝ≥0∞→GDriver→Measure UpperPlane)
    (hμ : Measurable (fun p : ℝ≥0∞×GDriver=>μ p.1 p.2))
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)]
    (hpos : ∀ᵐ b∂W,∀v : ℝ≥0∞,0<v → 0<μ v b univ) :
    ∃n : ℕ,0<∫⁻p,subdiskMass a μ (subdiskRadius n) 1 p∂finiteAngleLaw W a 1 := by
  have : IsProbabilityMeasure (finiteAngleLaw W a 1) := finiteAngleLaw_probability W hW a ha 1
  have hp : ∀ᵐ p∂finiteAngleLaw W a 1,
      0<diskMass a p.1.1 (μ (levelTime a p.1.1 p.2.1 1) p.2) (Metric.ball (0:ℂ) 1) := by
    have hb : ∀ᵐ p∂(angleLaw a).prod W,∀v : ℝ≥0∞,0<v → 0<μ v p.2 univ :=
      Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hpos
    filter_upwards [(finiteAngleLaw_absolutelyContinuous W a 1).ae_le hb] with p hp
    exact diskMass_unit_pos a p.1 _ (hp _ (centeredTime_pos a (by linarith) p.1 p.2 1 (by omega)))
  by_contra! hn
  have hzero (n : ℕ) : ∀ᵐ p∂finiteAngleLaw W a 1,subdiskMass a μ (subdiskRadius n) 1 p=0 :=
    (lintegral_eq_zero_iff (subdiskMass_measurable a ha μ hμ (subdiskRadius n) 1)).mp
      (le_antisymm (hn n) bot_le)
  have hf : ∀ᵐ p∂finiteAngleLaw W a 1,False := by
    filter_upwards [hp,ae_all_iff.mpr hzero] with p hp hz
    rw [unitBall_eq_iUnion_subdisk] at hp
    have hnull := measure_iUnion_null (fun n=>hz n)
    exact hp.ne' hnull
  simpa using ae_iff.mp hf

end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions KernelSimilarity

lemma cayley_subdisk_bounds (r : ℝ) (hr : 0≤r) (hr1 : r<1) (z : UpperPlane)
    (hz : ‖(z.1-Complex.I)/(z.1+Complex.I)‖≤r) :
    dist z.1 Complex.I≤2*r/(1-r) ∧ (1-r^2)/4≤z.1.im := by
  have hn : 1≤‖z.1+Complex.I‖ := by
    apply le_trans _ (Complex.im_le_norm _)
    simp only [Complex.add_im,Complex.I_im]
    linarith [z.2]
  have hp : 0<‖z.1+Complex.I‖ := lt_of_lt_of_le (by norm_num) hn
  have hz' : ‖z.1-Complex.I‖≤r*‖z.1+Complex.I‖ := by
    rw [norm_div] at hz
    exact (div_le_iff₀ hp).mp hz
  have htri : ‖z.1+Complex.I‖≤‖z.1-Complex.I‖+2 := by
    calc
      _ = ‖(z.1-Complex.I)+(Complex.I+Complex.I)‖ := by congr 1; ring
      _ ≤ ‖z.1-Complex.I‖+‖Complex.I+Complex.I‖ := norm_add_le _ _
      _ ≤ ‖z.1-Complex.I‖+2 := by
        have := norm_add_le Complex.I Complex.I
        simp only [Complex.norm_I] at this
        linarith
  constructor
  · rw [dist_eq_norm,le_div_iff₀ (sub_pos.mpr hr1)]
    nlinarith [mul_le_mul_of_nonneg_left htri hr]
  · have h2 : ‖z.1-Complex.I‖^2≤r^2*‖z.1+Complex.I‖^2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hz' 2
    have he : ‖z.1+Complex.I‖^2-‖z.1-Complex.I‖^2=4*z.1.im := by
      simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
        Complex.sub_re,Complex.sub_im,Complex.I_re,Complex.I_im,add_zero,sub_zero]
      ring
    have hrr : 0≤1-r^2 := by nlinarith
    have hsq : 1≤‖z.1+Complex.I‖^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq hrr]

lemma subdisk_region_compact (r : ℝ) (hr : 0≤r) (hr1 : r<1) :
    IsCompact {z : UpperPlane | dist z.1 Complex.I≤2*r/(1-r) ∧ (1-r^2)/4≤z.1.im} := by
  have hη : 0<(1-r^2)/4 := by nlinarith
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have he : (Subtype.val : UpperPlane→ℂ) ''
      {z | dist z.1 Complex.I≤2*r/(1-r) ∧ (1-r^2)/4≤z.1.im}=
      Metric.closedBall Complex.I (2*r/(1-r)) ∩ {z : ℂ | (1-r^2)/4≤z.im} := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩; exact hw
    · rintro ⟨hz,hi⟩
      exact ⟨⟨z,hη.trans_le hi⟩,⟨hz,hi⟩,rfl⟩
  rw [he]
  exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im)

lemma subdisk_cutoff_exists (r : ℝ) (hr : 0≤r) (hr1 : r<1) :
    ∃f : C_c(UpperPlane,ℝ),
      (∀z,0≤f z ∧ f z≤1) ∧
      (∀z : UpperPlane, ‖(z.1-Complex.I)/(z.1+Complex.I)‖≤r → f z=1) ∧
      (∀z∈tsupport f,(1-r^2)/8<z.1.im) := by
  have hη : 0<(1-r^2)/4 := by nlinarith
  obtain ⟨f,hf,hfc,hfs,h01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (subdisk_region_compact r hr hr1)
    (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_subtype_val))
    (show {z : UpperPlane | dist z.1 Complex.I≤2*r/(1-r) ∧ (1-r^2)/4≤z.1.im} ⊆
        {z : UpperPlane | (1-r^2)/8<z.1.im} from fun z hz=>by dsimp; linarith [hz.2])
  exact ⟨⟨f,hfc⟩,h01,fun z hz=>hf (cayley_subdisk_bounds r hr hr1 z hz),fun z hz=>hfs hz⟩

def subdiskCutoff (r : ℝ) (hr : 0≤r) (hr1 : r<1) : C_c(UpperPlane,ℝ) :=
  Classical.choose (subdisk_cutoff_exists r hr hr1)

lemma subdiskCutoff_nonneg (r : ℝ) (hr : 0≤r) (hr1 : r<1) (z : UpperPlane) :
    0≤ subdiskCutoff r hr hr1 z :=
  (Classical.choose_spec (subdisk_cutoff_exists r hr hr1)).1 z |>.1
lemma subdiskCutoff_le_one (r : ℝ) (hr : 0≤r) (hr1 : r<1) (z : UpperPlane) :
    subdiskCutoff r hr hr1 z≤1 :=
  (Classical.choose_spec (subdisk_cutoff_exists r hr hr1)).1 z |>.2
lemma subdiskCutoff_one (r : ℝ) (hr : 0≤r) (hr1 : r<1) (z : UpperPlane)
    (hz : ‖(z.1-Complex.I)/(z.1+Complex.I)‖≤r) : subdiskCutoff r hr hr1 z=1 :=
  (Classical.choose_spec (subdisk_cutoff_exists r hr hr1)).2.1 z hz
lemma subdiskCutoff_support (r : ℝ) (hr : 0≤r) (hr1 : r<1) (z : UpperPlane)
    (hz : z∈tsupport (subdiskCutoff r hr hr1)) : (1-r^2)/8<z.1.im :=
  (Classical.choose_spec (subdisk_cutoff_exists r hr hr1)).2.2 z hz

def subdiskTest (a : ℝ) (θ : Angle) (r : ℝ) (hr : 0≤r) (hr1 : r<1) : C_c(UpperPlane,ℝ) :=
  (2^(2-alpha a):ℝ) • normalizedTest a (Real.cos θ.1) (Real.sin θ.1)
    (Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2) (subdiskCutoff r hr hr1)

lemma subdiskTest_nonneg (a : ℝ) (θ : Angle) (r : ℝ) (hr : 0≤r) (hr1 : r<1)
    (z : UpperPlane) : 0≤ subdiskTest a θ r hr hr1 z :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (normalizedTest_nonneg a _ _ _ _ (subdiskCutoff_nonneg r hr hr1) z)

lemma subdiskTest_bound (a : ℝ) (θ : Angle) (r : ℝ) (hr : 0≤r) (hr1 : r<1)
    (z : UpperPlane) : ‖subdiskTest a θ r hr hr1 z‖≤2^(2-alpha a)*(Real.sin θ.1)^(alpha a-2) := by
  change ‖(2^(2-alpha a):ℝ)*normalizedTest a _ _ _ _ z‖≤_
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
  simpa only [one_mul] using normalizedTest_bound a _ _ _ (subdiskCutoff r hr hr1) (B:=1)
    (fun z=>by rw [Real.norm_eq_abs,abs_of_nonneg (subdiskCutoff_nonneg r hr hr1 z)]
               exact subdiskCutoff_le_one r hr hr1 z) z

lemma subdiskTest_support (a : ℝ) (θ : Angle) (r : ℝ) (hr : 0≤r) (hr1 : r<1) :
    Subtype.val '' tsupport (subdiskTest a θ r hr hr1) ⊆
      affine (Real.cos θ.1:ℂ) (Real.sin θ.1) (Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2) ''
        (Subtype.val '' tsupport (subdiskCutoff r hr hr1)) := by
  apply (image_mono (tsupport_smul_subset_right (fun _ : UpperPlane => (2^(2-alpha a):ℝ))
    (normalizedTest a (Real.cos θ.1) (Real.sin θ.1) (Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2)
      (subdiskCutoff r hr hr1)))).trans
  exact normalizedTest_support a _ _ _ _

lemma diskWeight_le_subdiskTest (a : ℝ) (ha : 1/4<a) (θ : Angle)
    (r : ℝ) (hr : 0≤r) (hr1 : r<1) (z : UpperPlane)
    (hz : diskMap θ.1 z.1∈Metric.closedBall (0:ℂ) r) :
    diskWeight a θ.1 z≤ subdiskTest a θ r hr hr1 z := by
  have hy := Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2
  have he : ‖((((upperAffine (Real.cos θ.1) (Real.sin θ.1) hy).symm z).1)-Complex.I)/
      ((((upperAffine (Real.cos θ.1) (Real.sin θ.1) hy).symm z).1)+Complex.I)‖≤r := by
    have h := diskMap_affine θ.1 θ.2.1 θ.2.2
      (((upperAffine (Real.cos θ.1) (Real.sin θ.1) hy).symm z).1)
    rw [←upperAffine_apply,Homeomorph.apply_symm_apply] at h
    simpa only [Metric.mem_closedBall,dist_zero_right,h] using hz
  change ‖deriv (diskMap θ.1) z.1‖^(2-alpha a)≤
    2^(2-alpha a)*((Real.sin θ.1)^(alpha a-2)*subdiskCutoff r hr hr1 _)
  rw [subdiskCutoff_one r hr hr1 _ he,mul_one]
  calc
    _ ≤ (2/(Real.sin θ.1))^(2-alpha a) := Real.rpow_le_rpow (norm_nonneg _)
      (disk_deriv_bound θ.1 θ.2.1 θ.2.2 z) (dimension_pos a ha).le
    _ = _ := by
      rw [div_eq_mul_inv,Real.mul_rpow (by norm_num : (0:ℝ)≤2) (inv_nonneg.mpr hy.le),
        Real.inv_rpow hy.le,←Real.rpow_neg hy.le,neg_sub]

lemma subdiskMass_le_enorm (a : ℝ) (ha : 1/4<a) (θ : Angle)
    (r : ℝ) (hr : 0≤r) (hr1 : r<1)
    (ν : Measure UpperPlane) [IsFiniteMeasureOnCompacts ν] :
    diskMass a θ.1 ν (Metric.closedBall (0:ℂ) r)≤‖∫z,subdiskTest a θ r hr hr1 z∂ν‖ₑ := by
  apply le_trans _ (Real.ofReal_le_enorm _)
  rw [diskMass,Measure.map_apply (diskMap_measurable θ.1) Metric.isClosed_closedBall.measurableSet,
    withDensity_apply _ ((diskMap_measurable θ.1) Metric.isClosed_closedBall.measurableSet),
    ofReal_integral_eq_lintegral_ofReal (subdiskTest a θ r hr hr1).integrable
      (Eventually.of_forall (subdiskTest_nonneg a θ r hr hr1)),
    ←lintegral_indicator ((diskMap_measurable θ.1) Metric.isClosed_closedBall.measurableSet)]
  apply lintegral_mono
  intro z
  by_cases hz : diskMap θ.1 z.1∈Metric.closedBall (0:ℂ) r
  · simp only [Set.indicator, Set.mem_preimage, hz, ite_true]
    exact ENNReal.ofReal_le_ofReal (diskWeight_le_subdiskTest a ha θ r hr hr1 z hz)
  · simp only [Set.indicator, Set.mem_preimage, hz, ite_false]; positivity

end SLEExactGauge.CenteredMoments
end
end

end OAI
