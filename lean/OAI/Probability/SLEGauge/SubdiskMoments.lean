import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.CenteredSequenceLaw

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen KernelSimilarity

 

theorem common_limit_subdisk_tilted_moment (r : ℝ) (hr : 0≤r) (hr1 : r<1)
    (a : ℝ) (ha : 1/4<a)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃D : ℝ≥0∞,D<∞ ∧ ∀(W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
      IsBrownianReal (fun t (b : ExactSLEGenerator.Driver)=>b.1 t) W →
      ∀(s : ℕ→Finset ℕ) (coeff : ℕ→ℕ→ℝ),
      (∀k j,j∈s k→0≤coeff k j) → (∀k,∑j∈s k,coeff k j=1) →
      ∀μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane,
      (∀b,IsFiniteMeasureOnCompacts (μ ∞ b)) → Measurable (μ ∞) →
      (∀ᵐ b∂W,∀v : ℝ≥0∞,μ v b≤μ ∞ b) →
      (∀ᵐ b∂W,∀f : C_c(UpperPlane,ℝ),Tendsto (fun k=>∑j∈s k,coeff k j*
        ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) ∞ b)
          atTop (𝓝 (∫z,f z∂μ ∞ b))) →
      ∀(θ : ℝ) (_hθ : 0<θ) (_hθπ : θ<Real.pi) (l : ℕ)
        (T : ExactSLEGenerator.Driver→ℝ≥0∞),
      (∫⁻b,(diskMass a θ (μ (T b) b) (Metric.closedBall (0:ℂ) r))^m
        ∂radialLaw W a (fromDisk θ 0) (Real.sin θ*Real.exp (-2*a*l)))≤
        D*ENNReal.ofReal ((Real.sin θ)^(-p a)) := by
  let K : Set ℂ := Subtype.val '' tsupport (subdiskCutoff r hr hr1)
  have hK : IsCompact K := (subdiskCutoff r hr hr1).hasCompactSupport.image continuous_subtype_val
  have hcK : ∀z∈K,(1-r^2)/4≤2*z.im := by
    rintro z ⟨w,hw,rfl⟩
    have hh := subdiskCutoff_support r hr hr1 w hw
    linarith
  obtain ⟨D,hD,hDb⟩ := actual_normalized_tilted_moment_bound a ha m hm K
    hK.measurableSet hK.isBounded ((1-r^2)/4) (by nlinarith) (by nlinarith [sq_nonneg r]) hcK
    (2^(2-alpha a)) (Real.rpow_nonneg (by norm_num) _)
  refine ⟨D,hD,?_⟩
  intro W hprob hW s coeff hcoeff hsum μ hμfin hμ hmono hlim θ hθ hθπ l T
  let (b : ExactSLEGenerator.Driver) : IsFiniteMeasureOnCompacts (μ ∞ b) := hμfin b
  let f := subdiskTest a ⟨θ,hθ,hθπ⟩ r hr hr1
  have hfm : Measurable (fun b=>∫z,f z∂μ ∞ b) := by
    let Kμ : Kernel ExactSLEGenerator.Driver UpperPlane := ⟨μ ∞,hμ⟩
    exact (f.continuous.stronglyMeasurable.integral_kernel (κ:=Kμ)).measurable
  have hb := hDb W hW θ hθ hθπ f (subdiskTest_support a ⟨θ,hθ,hθπ⟩ r hr hr1)
    (subdiskTest_bound a ⟨θ,hθ,hθπ⟩ r hr hr1) s coeff hcoeff hsum ∞ (μ ∞) hfm
    (hlim.mono (fun b hb=>hb f)) l
  refine le_trans (lintegral_mono_ae ?_) hb
  have habs : radialLaw W a (fromDisk θ 0) (Real.sin θ*Real.exp (-2*a*l)) ≪ W :=
    withDensity_absolutelyContinuous W _
  filter_upwards [habs.ae_le hmono] with b hb
  exact pow_le_pow_left' ((Measure.le_iff'.mp (diskMass_mono (hb (T b)) a θ)
    _).trans (subdiskMass_le_enorm a ha ⟨θ,hθ,hθπ⟩ r hr hr1 (μ ∞ b))) m

 

def subdiskMoment (W : Measure ExactSLEGenerator.Driver) (a : ℝ)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane) (r : ℝ) (m l : ℕ) : ℝ≥0∞ :=
  ∫⁻p,(subdiskMass a μ r l p)^m∂finiteAngleLaw W a l

 

theorem common_limit_subdisk_mixed_moment_bound (r : ℝ) (hr : 0≤r) (hr1 : r<1) (a : ℝ) (ha : 1/4<a)
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
      ∀l, subdiskMoment W a μ r m l≤D := by
  obtain ⟨C,hC,hCb⟩ := common_limit_subdisk_tilted_moment r hr hr1 a ha m hm
  let J := ∫⁻θ : Angle,ENNReal.ofReal (Real.sin θ.1^(-p a))∂angleLaw a
  refine ⟨C*J,ENNReal.mul_lt_top hC (angle_inverse_power_finite a),?_⟩
  intro W hprob hW s coeff hcoeff hsum μ hμfin hμ hmono hlim l
  let (v : ℝ≥0∞) (b : ExactSLEGenerator.Driver) : IsFiniteMeasureOnCompacts (μ v b) := hμfin v b
  rw [subdiskMoment,finiteAngleLaw_lintegral W a ha l _
    ((subdiskMass_measurable a ha μ hμ r l).pow_const m)]
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
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions CompactSequence

lemma subdiskMass_monotone (r a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    (b : ExactSLEGenerator.Driver) (hμ : Monotone (fun v=>μ v b)) (θ : Angle) :
    Monotone (fun l=>subdiskMass a μ r l (θ,b)) := by
  intro l k hlk
  exact Measure.le_iff'.mp (diskMass_mono
    (hμ (centeredTime_monotone a ha θ b hlk)) a θ.1) _

lemma subdiskMass_raw_measurable (r a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)] (θ : Angle) (l : ℕ)
    (hμ : Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
      (fun b=>μ (levelTime a θ.1 b.1 l) b)) :
    Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
      (fun b=>subdiskMass a μ r l (θ,b)) := by
  let : MeasurableSpace ExactSLEGenerator.Driver := (centeredTime_stopping a ha θ l).measurableSpace
  have hn := diskMass_joint_measurable a (fun _ : ExactSLEGenerator.Driver=>θ) measurable_const
    (fun b : ExactSLEGenerator.Driver=>μ (levelTime a θ.1 b.1 l) b) hμ
  exact (Measure.measurable_coe Metric.isClosed_closedBall.measurableSet).comp hn

lemma subdiskMass_raw_measurable_of_le (r a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)] (θ : Angle) {i l : ℕ} (hil : i≤l)
    (hμ : Measurable[(centeredTime_stopping a ha θ i).measurableSpace]
      (fun b=>μ (levelTime a θ.1 b.1 i) b)) :
    Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
      (fun b=>subdiskMass a μ r i (θ,b)) :=
  (subdiskMass_raw_measurable r a ha μ θ i hμ).mono
    ((centeredTime_stopping a ha θ i).measurableSpace_mono (centeredTime_stopping a ha θ l)
      (fun b=>centeredTime_monotone a ha θ b hil)) le_rfl

lemma subdisk_vector_consistent (W : Measure ExactSLEGenerator.Driver)
    [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver)=>b.1 t) W)
    (r a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    (hμ : Measurable (fun p : ℝ≥0∞×ExactSLEGenerator.Driver=>μ p.1 p.2))
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)]
    (hμraw : ∀l θ,Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
      (fun b=>μ (levelTime a θ.1 b.1 l) b))
    {l k : ℕ} (hlk : l≤k) :
    (finiteAngleLaw W a k).map (fun p=>fun i : Fin (l+1)=>subdiskMass a μ r i p)=
      (finiteAngleLaw W a l).map (fun p=>fun i : Fin (l+1)=>subdiskMass a μ r i p) := by
  have hm : Measurable (fun p=>fun i : Fin (l+1)=>subdiskMass a μ r i p) :=
    Measurable.of_eval (fun i=>subdiskMass_measurable a ha μ hμ r i)
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hm hA,Measure.map_apply hm hA]
  simp only [←lintegral_indicator_one (hm hA)]
  apply finiteAngleLaw_lintegral_consistent W hW a ha hlk
  · exact measurable_const.indicator (hm hA)
  · intro θ
    let : MeasurableSpace ExactSLEGenerator.Driver := (centeredTime_stopping a ha θ l).measurableSpace
    have hv : Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
        (fun b=>fun i : Fin (l+1)=>subdiskMass a μ r i (θ,b)) :=
      Measurable.of_eval (fun i=>subdiskMass_raw_measurable_of_le r a ha μ θ
        (by omega) (hμraw i θ))
    exact measurable_const.indicator (hv hA)

 

theorem exists_subdisk_sequence_law (W : Measure ExactSLEGenerator.Driver)
    [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver)=>b.1 t) W)
    (r a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    (hμ : Measurable (fun p : ℝ≥0∞×ExactSLEGenerator.Driver=>μ p.1 p.2))
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)]
    (hμraw : ∀l θ,Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
      (fun b=>μ (levelTime a θ.1 b.1 l) b))
    (hmono : ∀ᵐ b∂W,Monotone (fun v=>μ v b)) :
    ∃Q : Measure (ℕ→ℝ≥0∞),IsProbabilityMeasure Q ∧
      (∀n,Q.map (initialVector n)=(finiteAngleLaw W a n).map
        (fun p=>fun i : Fin (n+1)=>subdiskMass a μ r i p)) ∧
      (∀ᵐ x∂Q,Monotone x) := by
  have (n : ℕ) : IsProbabilityMeasure (finiteAngleLaw W a n) :=
    finiteAngleLaw_probability W hW a ha n
  obtain ⟨Q,hQ,hQlaw⟩ := exists_sequence_law (finiteAngleLaw W a)
    (subdiskMass a μ r) (subdiskMass_measurable a ha μ hμ r)
    (fun _ _ hlk=>subdisk_vector_consistent W hW r a ha μ hμ hμraw hlk)
  refine ⟨Q,hQ,hQlaw,?_⟩
  have hX (l : ℕ) : ∀ᵐ p∂finiteAngleLaw W a l,Monotone (fun n=>subdiskMass a μ r n p) := by
    have hb : ∀ᵐ p ∂(angleLaw a).prod W,Monotone (fun v=>μ v p.2) :=
      Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hmono
    filter_upwards [(finiteAngleLaw_absolutelyContinuous W a l).ae_le hb] with p hp
    exact subdiskMass_monotone r a ha μ p.2 hp p.1
  have hs (n : ℕ) : ∀ᵐ x∂Q,x n≤x (n+1) := by
    let i : Fin (n+1+1) := ⟨n,by omega⟩
    let j : Fin (n+1+1) := ⟨n+1,by omega⟩
    have hm : MeasurableSet {x : Fin (n+1+1)→ℝ≥0∞ | x i≤x j} :=
      measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _)
    change ∀ᵐ x∂Q,(initialVector (n+1) x) i≤(initialVector (n+1) x) j
    rw [←ae_map_iff (measurable_initialVector (n+1)).aemeasurable hm,hQlaw]
    apply (ae_map_iff (Measurable.of_eval
      (fun i : Fin (n+1+1)=>subdiskMass_measurable a ha μ hμ r i)).aemeasurable hm).mpr
    filter_upwards [hX (n+1)] with p hp
    exact hp (by simp only [i,j]; omega)
  filter_upwards [ae_all_iff.mpr hs] with x hx
  exact monotone_nat_of_le_succ hx

 

theorem subdiskSequence_moment (W : Measure ExactSLEGenerator.Driver)
    (r a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    (hμ : Measurable (fun p : ℝ≥0∞×ExactSLEGenerator.Driver=>μ p.1 p.2))
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)]
    (Q : Measure (ℕ→ℝ≥0∞))
    (hQlaw : ∀n,Q.map (initialVector n)=(finiteAngleLaw W a n).map
      (fun p=>fun i : Fin (n+1)=>subdiskMass a μ r i p))
    (hQmono : ∀ᵐ x∂Q,Monotone x) (m : ℕ) :
    (∫⁻x,(diskSequenceMass x)^m∂Q)=⨆l,subdiskMoment W a μ r m l := by
  simp only [diskSequenceMass,ENNReal.iSup_pow]
  rw [lintegral_iSup' (fun _=>(measurable_pi_apply _).pow_const m |>.aemeasurable)
    (hQmono.mono (fun _ hx _ _ hij=>pow_le_pow_left' (hx hij) m))]
  congr with l
  exact lintegral_coordinate Q (finiteAngleLaw W a l) (subdiskMass a μ r)
    (subdiskMass_measurable a ha μ hμ r) l (hQlaw l) (fun x=>x^m)
    (measurable_id.pow_const m)

 

theorem subdiskMoment_monotone (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver)=>b.1 t) W)
    (r a : ℝ) (ha : 1/4<a)
    (μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane)
    (hμ : Measurable (fun p : ℝ≥0∞×ExactSLEGenerator.Driver=>μ p.1 p.2))
    [∀v b,IsFiniteMeasureOnCompacts (μ v b)]
    (hμraw : ∀l θ,Measurable[(centeredTime_stopping a ha θ l).measurableSpace]
      (fun b=>μ (levelTime a θ.1 b.1 l) b))
    (hmono : ∀ᵐ b∂W,Monotone (fun v=>μ v b)) (m : ℕ) :
    Monotone (subdiskMoment W a μ r m) := by
  intro l k hlk
  rw [subdiskMoment,←finiteAngleLaw_lintegral_consistent W hW a ha hlk _
    ((subdiskMass_measurable a ha μ hμ r l).pow_const m)
    (fun θ=>(subdiskMass_raw_measurable r a ha μ θ l (hμraw l θ)).pow_const m)]
  apply lintegral_mono_ae
  have hb : ∀ᵐ p ∂(angleLaw a).prod W,Monotone (fun v=>μ v p.2) :=
    Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hmono
  filter_upwards [(finiteAngleLaw_absolutelyContinuous W a k).ae_le hb] with p hp
  exact pow_le_pow_left' (subdiskMass_monotone r a ha μ p.2 hp p.1 hlk) m

end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal Topology
namespace SLEExactGauge.PastMass
open ExactSLEGenerator ExactSLEMain ExactSLEGreen

 

def pastGreenKernel (W : Measure ExactSLEGenerator.Driver) (a : ℝ)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (z : UpperPlane) : ℝ≥0∞ :=
  (∫⁻b, ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1) ∂W) /
    ENNReal.ofReal (initialGreen a z)

lemma pastGreenKernel_measurable (W : Measure ExactSLEGenerator.Driver) [SFinite W]
    (a : ℝ) (ha : 1/4<a) (S : ExactSLEGenerator.Driver → ℝ≥0∞)
    (hS : IsStoppingTime rawFiltration S) : Measurable (pastGreenKernel W a S) :=
  ((stoppedSurvivingGreen_joint_measurable a ha S hS).ennreal_ofReal.lintegral_prod_left').div
    (initialGreen_continuous a).measurable.ennreal_ofReal

lemma initial_mul_pastGreenKernel (W : Measure ExactSLEGenerator.Driver)
    (a : ℝ) (S : ExactSLEGenerator.Driver → ℝ≥0∞) (z : UpperPlane) :
    ENNReal.ofReal (initialGreen a z) * pastGreenKernel W a S z =
      ∫⁻b, ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1) ∂W :=
  ENNReal.mul_div_cancel (ENNReal.ofReal_pos.mpr (initialGreen_pos a z)).ne'
    ENNReal.ofReal_ne_top

lemma pastGreenKernel_eq_ofReal (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (S : ExactSLEGenerator.Driver → ℝ≥0∞)
    (hS : IsStoppingTime rawFiltration S) (z : UpperPlane) :
    pastGreenKernel W a S z = ENNReal.ofReal
      ((∫b, stoppedSurvivingGreen a (S b) b z.1 ∂W) / initialGreen a z) := by
  rw [ENNReal.ofReal_div_of_pos (initialGreen_pos a z),
    ofReal_integral_eq_lintegral_ofReal (survivingGreen_optional_bound a ha W hW z S hS).1
      (Eventually.of_forall (fun b => stoppedSurvivingGreen_nonneg a (S b) b z.1))]
  rfl

lemma pastGreenKernel_le_one (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (S : ExactSLEGenerator.Driver → ℝ≥0∞)
    (hS : IsStoppingTime rawFiltration S) (z : UpperPlane) :
    pastGreenKernel W a S z ≤ 1 := by
  rw [pastGreenKernel_eq_ofReal W hW a ha S hS]
  exact (ENNReal.ofReal_le_ofReal ((div_le_one (initialGreen_pos a z)).mpr
    (survivingGreen_optional_bound a ha W hW z S hS).2)).trans_eq (by simp)

lemma pastGreenKernel_antitone (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (S T : ExactSLEGenerator.Driver → ℝ≥0∞)
    (hS : IsStoppingTime rawFiltration S) (hT : IsStoppingTime rawFiltration T)
    (hst : S ≤ T) (z : UpperPlane) :
    pastGreenKernel W a T z ≤ pastGreenKernel W a S z := by
  rw [pastGreenKernel_eq_ofReal W hW a ha T hT, pastGreenKernel_eq_ofReal W hW a ha S hS]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (initialGreen_pos a z).le
  simpa only [setIntegral_univ] using
    survivingGreen_optional_comparison a ha W hW z S T hS hT hst univ MeasurableSet.univ

 

lemma radialLaw_strict_past (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (S : ExactSLEGenerator.Driver → ℝ≥0∞)
    (hS : IsStoppingTime rawFiltration S) (z : UpperPlane)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1) :
    (radialLaw W a z.1 (z.1.im*q)) {b | S b < radialTime a b.1 z.1 (z.1.im*q)} =
      ENNReal.ofReal ((∫b, stoppedRemainingDensity a q (S b) b z.1 ∂W) / initialGreen a z) := by
  have hρ : 0<z.1.im*q := mul_pos z.2 hq
  have hr : z.1.im*q≤z.1.im := mul_le_of_le_one_right z.2.le hq1
  have hT := radialTime_stopping a (by linarith) z.1 z.2 _ hρ hr
  have hmS : Measurable S := hS.measurable'
  have hmT : Measurable (fun b : ExactSLEGenerator.Driver => radialTime a b.1 z.1 (z.1.im*q)) :=
    hT.measurable'
  have hE : MeasurableSet {b : ExactSLEGenerator.Driver | S b < radialTime a b.1 z.1 (z.1.im*q)} :=
    measurableSet_lt hmS hmT
  rw [radialLaw_apply W hW a ha z.1 z.2 _ hρ hr _ hE]
  have hp := (radial_conditional_weight_all W hW a ha z.1 z.2 _ hρ hr S hS
    univ MeasurableSet.univ).2
  simp only [setIntegral_univ] at hp
  rw [← integral_indicator hE]
  simp only [indicator_apply, mem_ofPred_eq]
  rw [hp]
  congr 1
  simp only [stoppedRemainingDensity_eq a q _ _ _ z.2, integral_const_mul, initialGreen]
  exact (mul_div_mul_left _ _ (Real.exp_ne_zero _)).symm

 

theorem radialLaw_strict_past_tendsto (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (S : ExactSLEGenerator.Driver → ℝ≥0∞)
    (hS : IsStoppingTime rawFiltration S) (z : UpperPlane)
    (q : ℕ → ℝ) (hq : ∀n, 0<q n ∧ q n≤1) (hq0 : Tendsto q atTop (𝓝 0)) :
    Tendsto (fun n => (radialLaw W a z.1 (z.1.im*q n))
      {b | S b < radialTime a b.1 z.1 (z.1.im*q n)}) atTop
      (𝓝 (pastGreenKernel W a S z)) := by
  simp_rw [radialLaw_strict_past W hW a ha S hS z _ (hq _).1 (hq _).2]
  rw [pastGreenKernel_eq_ofReal W hW a ha S hS]
  have he := stopped_remaining_integral_tendsto a ha W hW z S hS q hq hq0 univ
  simp only [setIntegral_univ] at he
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (he.div_const _)

end SLEExactGauge.PastMass
end
end
 

 
section
 

noncomputable section
open MeasureTheory Filter Set
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.PastMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

 
def finiteTestTime (F : Finset ℝ≥0) (M : ℝ≥0 → Ω → ℝ≥0∞)
    (H : ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  F.inf (fun q => if H < M q ω then (q : ℝ≥0∞) else ∞)

omit mΩ in
lemma finiteTestTime_lt_iff [MeasurableSpace Ω] (F : Finset ℝ≥0) (M : ℝ≥0 → Ω → ℝ≥0∞)
    (H : ℝ≥0∞) (ω : Ω) (v : ℝ≥0∞) :
    finiteTestTime F M H ω < v ↔ ∃ q ∈ F, H < M q ω ∧ (q : ℝ≥0∞) < v := by
  rw [finiteTestTime, Finset.inf_lt_iff]
  congr! 2 with q
  by_cases h : H < M q ω <;> simp [h]

omit mΩ in
lemma finiteTestTime_le_iff [MeasurableSpace Ω] (F : Finset ℝ≥0) (M : ℝ≥0 → Ω → ℝ≥0∞)
    (H : ℝ≥0∞) (ω : Ω) (t : ℝ≥0) :
    finiteTestTime F M H ω ≤ (t : ℝ≥0∞) ↔ ∃ q ∈ F, q ≤ t ∧ H < M q ω := by
  rw [finiteTestTime, Finset.inf_le_iff ENNReal.coe_lt_top]
  congr! 2 with q
  by_cases h : H < M q ω <;> simp [h]

lemma finiteTestTime_stopping (ℱ : Filtration ℝ≥0 mΩ)
    (M : ℝ≥0 → Ω → ℝ≥0∞) (hM : Adapted ℱ M)
    (F : Finset ℝ≥0) (H : ℝ≥0∞) :
    IsStoppingTime ℱ (finiteTestTime F M H) := by
  intro t
  change MeasurableSet[ℱ t] {ω | finiteTestTime F M H ω ≤ (t : ℝ≥0∞)}
  have he : {ω | finiteTestTime F M H ω ≤ (t : ℝ≥0∞)} =
      ⋃ q ∈ F, ⋃ (_ : q ≤ t), {ω | H < M q ω} := by
    ext ω
    simp only [mem_ofPred_eq, finiteTestTime_le_iff, mem_iUnion, exists_prop]
  rw [he]
  apply MeasurableSet.biUnion F.countable_toSet
  intro q hq
  apply MeasurableSet.iUnion
  intro hqt
  exact ℱ.mono hqt _ (measurableSet_lt measurable_const (hM q))

omit mΩ in
lemma finiteTestTime_antitone [MeasurableSpace Ω] (M : ℝ≥0 → Ω → ℝ≥0∞) (H : ℝ≥0∞)
    (ω : Ω) : Antitone (fun F : Finset ℝ≥0 => finiteTestTime F M H ω) := by
  intro F G hFG
  exact Finset.inf_mono hFG

 

lemma finiteTestTime_iUnion {ι : Type*} (e : ℕ → ι) (q : ι → ℝ≥0)
    (he : Function.Surjective e) (M : ℝ≥0 → Ω → ℝ≥0∞) (H : ℝ≥0∞)
    (ω : Ω) (v : ℝ≥0∞) :
    (∃ i, H < M (q i) ω ∧ (q i : ℝ≥0∞) < v) ↔
      ∃ n : ℕ, finiteTestTime ((Finset.range n).image (q ∘ e)) M H ω < v := by
  simp only [finiteTestTime_lt_iff, Finset.mem_image, Finset.mem_range,
    Function.comp_apply]
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨k,rfl⟩ := he i
    exact ⟨k+1,q (e k),⟨k,Nat.lt_succ_self k,rfl⟩,hi⟩
  · rintro ⟨n,t,⟨k,hk,rfl⟩,ht⟩
    exact ⟨e k,ht⟩

lemma finiteTestTime_sequence_antitone {ι : Type*} (e : ℕ → ι) (q : ι → ℝ≥0)
    (M : ℝ≥0 → Ω → ℝ≥0∞) (H : ℝ≥0∞) (ω : Ω) :
    Antitone (fun n => finiteTestTime ((Finset.range n).image (q ∘ e)) M H ω) := by
  intro n k hnk
  exact finiteTestTime_antitone M H ω (Finset.image_subset_image (Finset.range_mono hnk))

end SLEExactGauge.PastMass
end
end
 

 
section
 

noncomputable section
open MeasureTheory Filter Set
open scoped Classical NNReal ENNReal Topology
namespace SLEExactGauge.PastMass
open FlowIdentification ExactSLEGreen TraceMassContinuity TraceRestriction

 
def visitTime (κ : ℝ) (b : GDriver) : UpperPlane → ℝ≥0∞ :=
  firstVisit (fun z : UpperPlane => z.1) (internalTrace κ (driverHomeomorph.symm b))

lemma stopped_restriction_add (κ : ℝ) (b : GDriver)
    (μ : ℝ≥0∞ → Measure UpperPlane)
    (hμ : TraceMassFacts κ (driverHomeomorph.symm b) μ)
    (Q : Set UpperPlane) (hQ : MeasurableSet Q) (s : ℝ≥0∞) :
    μ s Q + μ ∞ (Q ∩ {z | s < visitTime κ b z}) = μ ∞ Q := by
  induction s using ENNReal.recTopCoe with
  | top => simp
  | coe s =>
    rw [hμ.firstVisit_identity s, Measure.restrict_apply hQ]
    have he : Q ∩ {z | (s : ℝ≥0∞) < visitTime κ b z} =
        Q \ {z | visitTime κ b z ≤ (s : ℝ≥0∞)} := by
      ext z
      simp only [mem_inter_iff,Set.mem_sdiff,mem_ofPred_eq,not_le]
    rw [he]
    exact measure_inter_add_sdiff Q (measurableSet_le hμ.firstVisit_measurable measurable_const)

lemma stopped_strictPast_mass (κ : ℝ) (b : GDriver)
    (μ : ℝ≥0∞ → Measure UpperPlane)
    (hμ : TraceMassFacts κ (driverHomeomorph.symm b) μ)
    (Q : Set UpperPlane) (hQ : MeasurableSet Q) (hfin : μ ∞ Q ≠ ∞) (s : ℝ≥0∞) :
    μ ∞ (Q ∩ {z | s < visitTime κ b z}) = μ ∞ Q - μ s Q := by
  have hsq : μ s Q ≠ ∞ := ne_top_of_le_ne_top hfin (hμ.monotone le_top Q)
  rw [← stopped_restriction_add κ b μ hμ Q hQ s, ENNReal.add_sub_cancel_left hsq]

lemma finite_past_mass (κ : ℝ) (b : GDriver)
    (μ : ℝ≥0∞ → Measure UpperPlane)
    (hμ : TraceMassFacts κ (driverHomeomorph.symm b) μ)
    (Q : Set UpperPlane) (hQ : MeasurableSet Q) (hfin : μ ∞ Q ≠ ∞)
    (F : Finset ℝ≥0) (H : ℝ≥0∞) :
    μ ∞ (Q ∩ {z | ∃q ∈ F, H < μ q Q ∧ (q : ℝ≥0∞) < visitTime κ b z}) =
      μ ∞ Q - μ (finiteTestTime F (fun q (_ : Unit) => μ q Q) H ()) Q := by
  simpa only [finiteTestTime_lt_iff] using
    stopped_strictPast_mass κ b μ hμ Q hQ hfin
      (finiteTestTime F (fun q (_ : Unit) => μ q Q) H ())

 

lemma all_past_mass_eq_iSup {ι : Type*} (e : ℕ → ι) (q : ι → ℝ≥0)
    (he : Function.Surjective e) (κ : ℝ) (b : GDriver)
    (μ : ℝ≥0∞ → Measure UpperPlane)
    (hμ : TraceMassFacts κ (driverHomeomorph.symm b) μ)
    (Q : Set UpperPlane) (hQ : MeasurableSet Q) (H : ℝ≥0∞) :
    μ ∞ (Q ∩ {z | ∃i, H < μ (q i) Q ∧ (q i : ℝ≥0∞) < visitTime κ b z}) =
      ⨆n : ℕ, μ ∞ (Q ∩ {z |
        finiteTestTime ((Finset.range n).image (q ∘ e))
          (fun q (_ : Unit) => μ q Q) H () < visitTime κ b z}) := by
  let A (n : ℕ) : Set UpperPlane := Q ∩ {z |
    finiteTestTime ((Finset.range n).image (q ∘ e))
      (fun q (_ : Unit) => μ q Q) H () < visitTime κ b z}
  have hA (n : ℕ) : MeasurableSet (A n) := hQ.inter
    (measurableSet_lt measurable_const hμ.firstVisit_measurable)
  have hAm : Monotone A := by
    intro n k hnk z hz
    exact ⟨hz.1,(finiteTestTime_sequence_antitone e q (fun q (_ : Unit) => μ q Q)
      H () hnk).trans_lt hz.2⟩
  have heq : Q ∩ {z | ∃i, H < μ (q i) Q ∧ (q i : ℝ≥0∞) < visitTime κ b z} =
      ⋃n : ℕ, A n := by
    ext z
    simp only [mem_inter_iff,mem_ofPred_eq,mem_iUnion,A,
      finiteTestTime_iUnion e q he (fun q (_ : Unit) => μ q Q) H ()]
    exact exists_and_left.symm
  rw [heq, hAm.measure_iUnion]

end SLEExactGauge.PastMass
end
end

end OAI
