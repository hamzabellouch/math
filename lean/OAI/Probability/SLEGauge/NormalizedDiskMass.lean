import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.HalfPlaneDistortion

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator CenteredMoments LoewnerScaling
open LoewnerGeometry MassVersions

lemma diskAt_fromDisk (θ : ℝ) : diskAt (fromDisk θ 0)=diskMap θ := by
  funext v
  rw [fromDisk_zero]
  have he : star (Complex.exp (Complex.I*θ))=Complex.exp (-Complex.I*θ) := by
    rw [Complex.star_def,←Complex.exp_conj]
    simp
  simp only [diskAt,he,diskMap]

lemma diskAt_scaled (c : ℝ) (hc : 0<c) (w v : ℂ) :
    diskAt ((c:ℂ)*w) ((c:ℂ)*v)=diskAt w v := by
  simp only [diskAt,Complex.star_def,map_mul,Complex.conj_ofReal,←mul_sub]
  exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hc.ne')

lemma diskAt_deriv_norm_scaled (c : ℝ) (hc : 0<c) (w v : UpperPlane) :
    ‖deriv (diskAt ((c:ℂ)*w.1)) ((c:ℂ)*v.1)‖=c⁻¹*‖deriv (diskAt w.1) v.1‖ := by
  have hw : 0<((c:ℂ)*w.1).im := by simpa [Complex.mul_im] using mul_pos hc w.2
  have hv : 0<((c:ℂ)*v.1).im := by simpa [Complex.mul_im] using mul_pos hc v.2
  rw [diskAt_deriv_norm hw hv,diskAt_deriv_norm w.2 v.2]
  simp only [Complex.star_def,map_mul,Complex.conj_ofReal,←mul_sub,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hc,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,add_zero]
  field_simp

 
def pointDiskRegion (w : UpperPlane) (q : ℝ) : Set UpperPlane := {v | ‖diskAt w.1 v.1‖≤q}

def pointDiskWeight (a : ℝ) (w : UpperPlane) (v : UpperPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (‖deriv (diskAt w.1) v.1‖^(2-alpha a))

def pointDiskMass (a : ℝ) (w : UpperPlane) (q : ℝ) (ν : Measure UpperPlane) : ℝ≥0∞ :=
  ∫⁻v in pointDiskRegion w q,pointDiskWeight a w v∂ν

lemma pointDiskRegion_measurable (w : UpperPlane) (q : ℝ) : MeasurableSet (pointDiskRegion w q) := by
  unfold pointDiskRegion diskAt
  exact measurableSet_le (by fun_prop) measurable_const

lemma pointDiskWeight_measurable (a : ℝ) (w : UpperPlane) : Measurable (pointDiskWeight a w) := by
  have he : pointDiskWeight a w=fun v : UpperPlane=>ENNReal.ofReal
      ((2*w.1.im/‖v.1-star w.1‖^2)^(2-alpha a)) := by
    funext v
    rw [pointDiskWeight,diskAt_deriv_norm w.2 v.2]
  rw [he]
  fun_prop

lemma pointDiskMass_diskMass (a θ q : ℝ) (ν : Measure UpperPlane)
    (hθ : 0<θ) (hθπ : θ<Real.pi) :
    pointDiskMass a ⟨fromDisk θ 0,by
      rw [fromDisk_zero_im]
      exact Real.sin_pos_of_pos_of_lt_pi hθ hθπ⟩ q ν =
      diskMass a θ ν (Metric.closedBall 0 q) := by
  rw [diskMass,Measure.map_apply (diskMap_measurable θ) Metric.isClosed_closedBall.measurableSet,
    withDensity_apply _ ((diskMap_measurable θ) Metric.isClosed_closedBall.measurableSet)]
  simp only [pointDiskMass,pointDiskWeight,pointDiskRegion,diskAt_fromDisk,diskWeight,
    Set.preimage,Metric.mem_closedBall,dist_zero_right]

lemma pointDiskMass_smul (a : ℝ) (w : UpperPlane) (q : ℝ) (ν : Measure UpperPlane) (c : ℝ≥0∞) :
    pointDiskMass a w q (c•ν)=c*pointDiskMass a w q ν := by
  rw [pointDiskMass,Measure.restrict_smul,lintegral_smul_measure,smul_eq_mul]
  rfl

lemma pointDiskMass_map_dilation (a : ℝ) {c : ℝ≥0} (hc : 0<c) (w : UpperPlane)
    (q : ℝ) (ν : Measure UpperPlane) :
    pointDiskMass a (upperDilation c hc w) q (ν.map (upperDilation c hc))=
      ENNReal.ofReal ((c:ℝ)^(alpha a-2))*pointDiskMass a w q ν := by
  rw [pointDiskMass,←lintegral_indicator (pointDiskRegion_measurable _ q),
    (upperDilation c hc).measurableEmbedding.lintegral_map]
  have he (v : UpperPlane) :
      (pointDiskRegion (upperDilation c hc w) q).indicator
        (pointDiskWeight a (upperDilation c hc w)) (upperDilation c hc v)=
        ENNReal.ofReal ((c:ℝ)^(alpha a-2))*(pointDiskRegion w q).indicator
          (pointDiskWeight a w) v := by
    have hreg : upperDilation c hc v∈pointDiskRegion (upperDilation c hc w) q ↔
        v∈pointDiskRegion w q := by
      change ‖diskAt (((c:ℝ):ℂ)*w.1) (((c:ℝ):ℂ)*v.1)‖≤q ↔ _
      rw [diskAt_scaled (c:ℝ) hc]
      rfl
    by_cases hv : v∈pointDiskRegion w q
    · rw [indicator_of_mem (hreg.mpr hv),indicator_of_mem hv]
      rw [pointDiskWeight,upperDilation_apply,upperDilation_apply,
        diskAt_deriv_norm_scaled _ (show 0<(c:ℝ) from hc) w v,Real.mul_rpow (inv_nonneg.mpr c.coe_nonneg) (norm_nonneg _),
        Real.inv_rpow c.coe_nonneg,←Real.rpow_neg c.coe_nonneg,neg_sub,
        ENNReal.ofReal_mul (Real.rpow_nonneg c.coe_nonneg _)]
      rfl
    · rw [indicator_of_notMem (hreg.not.mpr hv),indicator_of_notMem hv,mul_zero]
  simp_rw [he]
  rw [lintegral_const_mul _ ((pointDiskWeight_measurable a w).indicator (pointDiskRegion_measurable w q)),
    lintegral_indicator (pointDiskRegion_measurable w q)]
  rfl

 
lemma pointDiskMass_recovered_scaled (a : ℝ) (ha : 1/4<a) {c : ℝ≥0} (hc : 0<c)
    (s : ℕ→Finset ℕ) (v : ℕ→ℕ→ℝ) (hv : ∀k j,j∈s k→0≤v k j)
    (t : ℝ≥0∞) (b : GDriver) (w : UpperPlane) (q : ℝ) :
    pointDiskMass a w q (recoveredMass a ha s v hv t (scaleDriver c b))=
      pointDiskMass a (upperDilation c hc w) q
        (recoveredMass a ha s v hv ((c:ℝ≥0∞)^2*t) b) := by
  have he := pointDiskMass_map_dilation a hc w q (recoveredMass a ha s v hv t (scaleDriver c b))
  rw [map_recoveredMass_scaled a ha hc,pointDiskMass_smul] at he
  exact (ENNReal.mul_right_inj
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (show 0<(c:ℝ) from hc) _)).ne'
    ENNReal.ofReal_ne_top).mp he.symm

 

lemma normalized_subdiskMass_eq (a : ℝ) (ha : 1/4<a)
    (s : ℕ→Finset ℕ) (v : ℕ→ℕ→ℝ) (hv : ∀k j,j∈s k→0≤v k j)
    (w : UpperPlane) (b : GDriver) (q : ℝ) (l : ℕ) :
    subdiskMass a (recoveredMass a ha s v hv) q l (pointAngle w,normalizeDriver w b)=
      pointDiskMass a w q (recoveredMass a ha s v hv
        ((‖w.1‖₊:ℝ≥0∞)^2*levelTime a (pointAngle w).1 (normalizeDriver w b).1 l) b) := by
  let w₀ : UpperPlane := ⟨fromDisk (pointAngle w).1 0,by
    rw [fromDisk_zero_im]
    exact Real.sin_pos_of_pos_of_lt_pi (pointAngle w).2.1 (pointAngle w).2.2⟩
  have he : upperDilation ‖w.1‖₊ (point_norm_pos w) w₀=w := by
    apply Subtype.ext
    exact norm_mul_fromDisk_pointAngle w
  change diskMass a (pointAngle w).1 _ (Metric.closedBall 0 q)=_
  rw [←pointDiskMass_diskMass a (pointAngle w).1 q _ (pointAngle w).2.1 (pointAngle w).2.2]
  change pointDiskMass a w₀ q (recoveredMass a ha s v hv _ (scaleDriver ‖w.1‖₊ b))=_
  rw [pointDiskMass_recovered_scaled a ha (point_norm_pos w),he]

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator CenteredMoments LoewnerScaling
open LoewnerGeometry MassVersions TraceMassContinuity

lemma inverseUpper_measurableEmbedding (a : ℝ) (ha : 1/4<a) (b : GDriver) (t : ℝ≥0) :
    MeasurableEmbedding (inverseUpper a (lt_trans (by norm_num) ha) b t) := by
  have hs : MeasurableSet {z : UpperPlane | alive a b.1 t z.1} :=
    (measurableSet_alive_joint a ha).preimage
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  exact (MeasurableEmbedding.subtype_coe hs).comp
    (restartHomeomorph a (lt_trans (by norm_num) ha) b t).measurableEmbedding

 

def spatialDiskRegion (a : ℝ) (ha : 0<a) (b : GDriver) (t : ℝ≥0)
    (w : UpperPlane) (q : ℝ) : Set UpperPlane :=
  inverseUpper a ha b t '' pointDiskRegion w q

lemma spatialDiskRegion_measurable (a : ℝ) (ha : 1/4<a) (b : GDriver) (t : ℝ≥0)
    (w : UpperPlane) (q : ℝ) :
    MeasurableSet (spatialDiskRegion a (lt_trans (by norm_num) ha) b t w q) :=
  (inverseUpper_measurableEmbedding a ha b t).measurableSet_image.mpr (pointDiskRegion_measurable w q)

lemma spatialDiskRegion_subset_alive (a : ℝ) (ha : 0<a) (b : GDriver) (t : ℝ≥0)
    (w : UpperPlane) (q : ℝ) :
    spatialDiskRegion a ha b t w q ⊆ {z : UpperPlane | alive a b.1 t z.1} := by
  rintro _ ⟨v,_,rfl⟩
  exact inverseMap_alive ha b t v.2

lemma subtype_spatialDiskRegion (a : ℝ) (ha : 0<a) (b : GDriver) (t : ℝ≥0)
    (w : UpperPlane) (q : ℝ) :
    Subtype.val '' spatialDiskRegion a ha b t w q=inverseMap a b t '' centeredRegion w.1 q := by
  ext z
  constructor
  · rintro ⟨u,⟨v,hv,rfl⟩,rfl⟩
    exact ⟨v.1,⟨v.2,hv⟩,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    exact ⟨inverseUpper a ha b t ⟨v,hv.1⟩,⟨⟨v,hv.1⟩,hv.2,rfl⟩,rfl⟩

lemma restartPush_spatialDisk (a : ℝ) (ha : 1/4<a) (b : GDriver) (t : ℝ≥0)
    (w : UpperPlane) (q : ℝ) (ν : Measure UpperPlane) :
    restartPush a (lt_trans (by norm_num) ha) b t ν
      (spatialDiskRegion a (lt_trans (by norm_num) ha) b t w q)=
      ∫⁻v in pointDiskRegion w q,restartWeight a b t v∂ν := by
  rw [restartPush,(inverseUpper_measurableEmbedding a ha b t).map_apply,
    spatialDiskRegion,preimage_image_eq _ (inverseUpper_injective _ _ _ _),
    withDensity_apply _ (pointDiskRegion_measurable w q)]

 

def diskLower (q : ℝ) : ℝ := (2*subdiskDistortion q)⁻¹
def diskUpper (q : ℝ) : ℝ := subdiskDistortion q*(subdiskReach q+2)^2/2

lemma diskLower_pos (q : ℝ) : 0<diskLower q := by
  have hd := subdiskDistortion_pos q
  unfold diskLower
  positivity
lemma diskUpper_pos {q : ℝ} (hq : 0≤q) (hq1 : q<1) : 0<diskUpper q := by
  have hd := subdiskDistortion_pos q
  have hr := subdiskReach_nonneg hq hq1
  unfold diskUpper
  positivity

lemma restartWeight_disk_bounds (a : ℝ) (ha : 1/4<a) (b : GDriver) (t : ℝ≥0)
    (w : UpperPlane) {q : ℝ} (hq : 0≤q) (hq1 : q<1) (v : UpperPlane)
    (hv : v∈pointDiskRegion w q) :
    ENNReal.ofReal ((diskLower q*(w.1.im*‖deriv (inverseMap a b t) w.1‖))^(2-alpha a)) *
        pointDiskWeight a w v ≤ restartWeight a b t v ∧
    restartWeight a b t v ≤
      ENNReal.ofReal ((diskUpper q*(w.1.im*‖deriv (inverseMap a b t) w.1‖))^(2-alpha a)) *
        pointDiskWeight a w v := by
  have ha0 : 0<a := by linarith
  have hd : 0<‖deriv (diskAt w.1) v.1‖ := by
    rw [diskAt_deriv_norm w.2 v.2]
    exact div_pos (mul_pos (by norm_num) w.2)
      (sq_pos_of_pos (norm_pos_iff.mpr (diskAt_denominator_ne w.2 v.2)))
  have hb := centered_disk_deriv_ratio ha0 b t w.2 hq hq1 ⟨v.2,hv⟩
  have hlow : diskLower q*(w.1.im*‖deriv (inverseMap a b t) w.1‖)*‖deriv (diskAt w.1) v.1‖≤
      ‖deriv (inverseMap a b t) v.1‖ := by
    have hh := (le_div_iff₀ hd).mp hb.1
    simpa only [diskLower,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hh
  have hupp : ‖deriv (inverseMap a b t) v.1‖≤
      (diskUpper q*(w.1.im*‖deriv (inverseMap a b t) w.1‖))*‖deriv (diskAt w.1) v.1‖ :=
    (div_le_iff₀ hd).mp hb.2
  have hl0 : 0≤diskLower q*(w.1.im*‖deriv (inverseMap a b t) w.1‖) :=
    mul_nonneg (diskLower_pos q).le (mul_nonneg w.2.le (norm_nonneg _))
  have hu0 : 0≤diskUpper q*(w.1.im*‖deriv (inverseMap a b t) w.1‖) :=
    mul_nonneg (diskUpper_pos hq hq1).le (mul_nonneg w.2.le (norm_nonneg _))
  constructor
  · have hh := ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (mul_nonneg hl0 hd.le)
      hlow (dimension_pos a ha).le)
    rw [Real.mul_rpow hl0 hd.le,ENNReal.ofReal_mul (Real.rpow_nonneg hl0 _)] at hh
    exact hh
  · have hh := ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) hupp (dimension_pos a ha).le)
    rw [Real.mul_rpow hu0 hd.le,ENNReal.ofReal_mul (Real.rpow_nonneg hu0 _)] at hh
    exact hh

 

theorem restartPush_disk_bounds (a : ℝ) (ha : 1/4<a) (b : GDriver) (t : ℝ≥0)
    (w : UpperPlane) {q : ℝ} (hq : 0≤q) (hq1 : q<1) (ν : Measure UpperPlane) :
    ENNReal.ofReal ((diskLower q*(w.1.im*‖deriv (inverseMap a b t) w.1‖))^(2-alpha a)) *
        pointDiskMass a w q ν ≤
      restartPush a (lt_trans (by norm_num) ha) b t ν
        (spatialDiskRegion a (lt_trans (by norm_num) ha) b t w q) ∧
    restartPush a (lt_trans (by norm_num) ha) b t ν
        (spatialDiskRegion a (lt_trans (by norm_num) ha) b t w q) ≤
      ENNReal.ofReal ((diskUpper q*(w.1.im*‖deriv (inverseMap a b t) w.1‖))^(2-alpha a)) *
        pointDiskMass a w q ν := by
  rw [restartPush_spatialDisk a ha,pointDiskMass,←lintegral_const_mul _ (pointDiskWeight_measurable a w),
    ←lintegral_const_mul _ (pointDiskWeight_measurable a w)]
  constructor
  · exact setLIntegral_mono' (pointDiskRegion_measurable w q)
      (fun v hv=>(restartWeight_disk_bounds a ha b t w hq hq1 v hv).1)
  · exact setLIntegral_mono' (pointDiskRegion_measurable w q)
      (fun v hv=>(restartWeight_disk_bounds a ha b t w hq hq1 v hv).2)

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator CenteredMoments LoewnerScaling
open LoewnerGeometry MassVersions TraceMassContinuity

 

def radialDiskRegion (a : ℝ) (ha : 0<a) (z : ℂ) (σ q : ℝ) (b : GDriver) : Set UpperPlane :=
  spatialDiskRegion a ha b (radialTime a b.1 z σ).toNNReal (radialPoint a z σ b) q

lemma radialPoint_spatial_radius (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (σ : ℝ) (hσ : 0<σ) (hσz : σ≤z.im) (b : GDriver)
    (hb : radialTime a b.1 z σ≠∞) :
    (radialPoint a z σ b).1.im *
      ‖deriv (inverseMap a b (radialTime a b.1 z σ).toNNReal) (radialPoint a z σ b).1‖=σ := by
  have hs := radialTime_attained a ha z hz σ hσ hσz b hb
  rw [radialPoint_eq a ha z hz σ hσ hσz b hb]
  change (loewnerMap a b.1 _ z-(b.1 _:ℂ)).im*‖deriv (inverseMap a b _)
    (loewnerMap a b.1 _ z-(b.1 _:ℂ))‖=σ
  rw [inverseMap_spatial_radius ha b _ hs.1,hs.2]

lemma radialDiskRegion_localization (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (σ : ℝ) (hσ : 0<σ) (hσz : σ≤z.im) {q : ℝ} (hq : 1/2≤q) (hq1 : q<1)
    (b : GDriver) (hb : radialTime a b.1 z σ≠∞) :
    (Subtype.val : UpperPlane→ℂ) ⁻¹' closedBall z (σ/200) ⊆ radialDiskRegion a ha z σ q b ∧
    radialDiskRegion a ha z σ q b ⊆
      (Subtype.val : UpperPlane→ℂ) ⁻¹' closedBall z (subdiskReach q*subdiskDistortion q*σ) := by
  have hs := radialTime_attained a ha z hz σ hσ hσz b hb
  have hh := centered_localization_at_alive ha b _ hs.1 hq hq1
  rw [hs.2] at hh
  have he : (Subtype.val : UpperPlane→ℂ) '' radialDiskRegion a ha z σ q b=
      inverseMap a b (radialTime a b.1 z σ).toNNReal ''
        centeredRegion (loewnerMap a b.1 (radialTime a b.1 z σ).toNNReal z-
          (b.1 (radialTime a b.1 z σ).toNNReal:ℂ)) q := by
    rw [radialDiskRegion,subtype_spatialDiskRegion,radialPoint_eq a ha z hz σ hσ hσz b hb]
    rfl
  constructor
  · intro u hu
    obtain ⟨v,hv,heq⟩ := (he ▸ hh.1 hu)
    exact (Subtype.ext heq : v=u) ▸ hv
  · intro u hu
    exact hh.2 (he ▸ mem_image_of_mem Subtype.val hu)

 

theorem actual_radial_spatial_bounds (κ a : ℝ) (ha : 1/4<a) (W : Measure GDriver)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    (D : CanonicalMassData κ a ha W (recoveredMass a ha s c hc))
    (z : ℂ) (hz : 0<z.im) (σ : ℝ) (hσ : 0<σ) (hσz : σ≤z.im)
    (q : ℝ) (hq : 0≤q) (hq1 : q<1) :
    let μ := recoveredMass a ha s c hc
    let S := fun b : GDriver=>radialTime a b.1 z σ
    let R := radialDiskRegion a (lt_trans (by norm_num) ha) z σ q
    ∀ᵐ b∂W,S b≠∞→μ (S b) b (R b)=0 ∧ ∀l : ℕ,
      ENNReal.ofReal ((diskLower q*σ)^(2-alpha a))*normalizedTest a z σ (subdiskMass a μ q l) b ≤
        μ (radialTime a b.1 z (σ*Real.exp (-2*a*l))) b (R b) ∧
      μ (radialTime a b.1 z (σ*Real.exp (-2*a*l))) b (R b) ≤
        ENNReal.ofReal ((diskUpper q*σ)^(2-alpha a))*normalizedTest a z σ (subdiskMass a μ q l) b := by
  dsimp only
  let μ := recoveredMass a ha s c hc
  let S := fun b : GDriver=>radialTime a b.1 z σ
  let ha0 : 0<a := lt_trans (by norm_num) ha
  have hS := radialTime_stopping a ha0 z hz σ hσ hσz
  filter_upwards [D.restart S hS] with b hb
  intro hbf
  have hrest := hb hbf
  let R := radialDiskRegion a ha0 z σ q b
  have hR : MeasurableSet R := spatialDiskRegion_measurable a ha b _ _ q
  have hRA : R⊆{u : UpperPlane | alive a b.1 (S b).toNNReal u.1} :=
    spatialDiskRegion_subset_alive a ha0 b _ _ q
  have hzero : μ (S b) b R=0 := by
    have hh := congrArg (fun ν : Measure UpperPlane=>ν R) hrest.1
    rwa [Measure.restrict_apply hR,inter_eq_left.mpr hRA,Measure.coe_zero,Pi.zero_apply] at hh
  refine ⟨hzero,?_⟩
  intro l
  let w := radialPoint a z σ b
  let t := (‖w.1‖₊:ℝ≥0∞)^2*levelTime a (pointAngle w).1 (normalizeDriver w (restartAt S b)).1 l
  have ht : S b+t=radialTime a b.1 z (σ*Real.exp (-2*a*l)) :=
    normalized_levelTime_restart a ha0 z hz σ hσ hσz l b hbf
  have he : μ (radialTime a b.1 z (σ*Real.exp (-2*a*l))) b R=
      restartPush a ha0 b (S b).toNNReal (μ t (restartAt S b)) R := by
    have hh := congrArg (fun ν : Measure UpperPlane=>ν R) (hrest.2 t)
    rwa [Measure.restrict_apply hR,inter_eq_left.mpr hRA,ht] at hh
  have hbounds := restartPush_disk_bounds a ha b (S b).toNNReal w hq hq1 (μ t (restartAt S b))
  rw [radialPoint_spatial_radius a ha0 z hz σ hσ hσz b hbf] at hbounds
  have hnorm : normalizedTest a z σ (subdiskMass a μ q l) b=
      pointDiskMass a w q (μ t (restartAt S b)) :=
    normalized_subdiskMass_eq a ha s c hc w (restartAt S b) q l
  change ENNReal.ofReal ((diskLower q*σ)^(2-alpha a))*normalizedTest a z σ (subdiskMass a μ q l) b≤
      μ (radialTime a b.1 z (σ*Real.exp (-2*a*l))) b R ∧ _
  rw [hnorm,he]
  exact hbounds

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.PastMass
open FlowIdentification ExactSLEGreen TraceMassContinuity TraceRestriction

lemma denseRange_nnrat_nnreal : DenseRange (fun q : ℚ≥0 => (q : ℝ≥0)) := by
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨q,haq,hqb⟩ := exists_rat_btwn (show (a : ℝ)<(b : ℝ) from hab)
  have hq : 0≤q := Rat.cast_nonneg.mp ((a.2.trans haq.le) : (0 : ℝ)≤q)
  let r : ℚ≥0 := ⟨q,hq⟩
  refine ⟨(r : ℝ≥0),⟨r,rfl⟩,?_,?_⟩
  · change (a : ℝ) < (r : ℝ)
    simpa only [r,NNRat.cast_mk] using haq
  · change (r : ℝ) < (b : ℝ)
    simpa only [r,NNRat.cast_mk] using hqb

 

lemma accumulated_continuous (κ : ℝ) (hκ : 0<κ) (b : GDriver)
    (μ : ℝ≥0∞→Measure UpperPlane)
    (hμ : TraceMassFacts κ (driverHomeomorph.symm b) μ)
    (Q : Set UpperPlane) (hQ : MeasurableSet Q) (hfin : μ ∞ Q≠∞) :
    Continuous (fun t : ℝ≥0 => (μ t Q).toReal) := by
  let := hμ.atomless
  let f : UpperPlane→ℝ := Q.indicator (fun _=>1)
  have hf : Integrable f (μ ∞) := (integrable_indicator_iff hQ).mpr (integrableOn_const hfin)
  have hγ := continuous_internalTrace hκ _ hμ.continuous_trace
  have hc := continuous_integral_visited (μ ∞) (fun z : UpperPlane=>z.1)
    measurable_subtype_coe Subtype.val_injective _ hγ f hf
  have he (t : ℝ≥0) : (∫z in visited (fun z : UpperPlane=>z.1)
      (internalTrace κ (driverHomeomorph.symm b)) t,f z∂μ ∞) = (μ t Q).toReal := by
    rw [←hμ.restriction]
    simp only [f,integral_indicator hQ,integral_const,Measure.real,
      Measure.restrict_apply_univ,smul_eq_mul,mul_one]
  simpa only [he] using hc

lemma accumulated_zero (κ : ℝ) (b : GDriver) (μ : ℝ≥0∞→Measure UpperPlane)
    (hμ : TraceMassFacts κ (driverHomeomorph.symm b) μ) : μ 0=0 := by
  simpa only [ENNReal.coe_zero,not_lt_zero,ofPred_false,Measure.restrict_empty] using
    hμ.strict_firstVisit_identity 0

 

lemma exists_rational_threshold (κ : ℝ) (hκ : 0<κ) (b : GDriver)
    (μ : ℝ≥0∞→Measure UpperPlane)
    (hμ : TraceMassFacts κ (driverHomeomorph.symm b) μ)
    (Q : Set UpperPlane) (hQ : MeasurableSet Q) (hfin : μ ∞ Q≠∞)
    (H U : ℝ) (hH : 0≤H) (hHU : H<U) (hUM : U<(μ ∞ Q).toReal) :
    ∃q : ℚ≥0,H<(μ ((q : ℝ≥0) : ℝ≥0∞) Q).toReal ∧
      (μ ((q : ℝ≥0) : ℝ≥0∞) Q).toReal<U := by
  let M : ℝ≥0→ℝ := fun t=>(μ t Q).toReal
  have hM : Continuous M := accumulated_continuous κ hκ b μ hμ Q hQ hfin
  have hzero : M 0=0 := by simp [M,accumulated_zero κ b μ hμ]
  have hlim : Tendsto (fun n : ℕ=>M (n:ℝ≥0)) atTop (𝓝 (μ ∞ Q).toReal) :=
    (ENNReal.tendsto_toReal hfin).comp (hμ.exhaustion Q hQ)
  obtain ⟨n,hn⟩ := (hlim.eventually (eventually_gt_nhds hUM)).exists
  have hmid : (H+U)/2∈Icc (M 0) (M (n:ℝ≥0)) := by rw [hzero]; constructor <;> linarith
  obtain ⟨t,ht⟩ := intermediate_value_univ (0:ℝ≥0) (n:ℝ≥0) hM hmid
  exact denseRange_nnrat_nnreal.exists_mem_open (isOpen_Ioo.preimage hM)
    ⟨t,by change H<M t ∧ M t<U; rw [ht]; constructor <;> linarith⟩

 

lemma mass_le_twice_strict_past (κ : ℝ) (hκ : 0<κ) (b : GDriver)
    (μ : ℝ≥0∞→Measure UpperPlane)
    (hμ : TraceMassFacts κ (driverHomeomorph.symm b) μ)
    (Q : Set UpperPlane) (hQ : MeasurableSet Q) (hfin : μ ∞ Q≠∞)
    (H : ℝ) (hH : 0≤H) (hbad : 2*ENNReal.ofReal H<μ ∞ Q) :
    μ ∞ Q ≤ 2*μ ∞ (Q∩{z | ∃q : ℚ≥0,
      ENNReal.ofReal H<μ ((q:ℝ≥0):ℝ≥0∞) Q ∧ ((q:ℝ≥0):ℝ≥0∞)<visitTime κ b z}) := by
  have hbadReal : 2*H<(μ ∞ Q).toReal := by
    apply (ENNReal.ofReal_lt_iff_lt_toReal (mul_nonneg (by norm_num) hH) hfin).mp
    simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat] using hbad
  have hMpos : 0<(μ ∞ Q).toReal := by linarith
  obtain ⟨q,hqH,hqM⟩ := exists_rational_threshold κ hκ b μ hμ Q hQ hfin
    H ((μ ∞ Q).toReal/2) hH (by linarith) (by linarith)
  have hqle : μ ((q:ℝ≥0):ℝ≥0∞) Q≤μ ∞ Q := hμ.monotone le_top Q
  have hqfin : μ ((q:ℝ≥0):ℝ≥0∞) Q≠∞ := ne_top_of_le_ne_top hfin hqle
  have hqH' : ENNReal.ofReal H<μ ((q:ℝ≥0):ℝ≥0∞) Q :=
    (ENNReal.ofReal_lt_iff_lt_toReal hH hqfin).mpr hqH
  have hhalf : μ ∞ Q≤2*(μ ∞ Q-μ ((q:ℝ≥0):ℝ≥0∞) Q) := by
    apply (ENNReal.toReal_le_toReal hfin (ENNReal.mul_ne_top (by norm_num)
      (ne_top_of_le_ne_top hfin tsub_le_self))).mp
    rw [ENNReal.toReal_mul,ENNReal.toReal_sub_of_le hqle hfin]
    norm_num only [ENNReal.toReal_ofNat]
    linarith
  calc
    μ ∞ Q≤2*(μ ∞ Q-μ ((q:ℝ≥0):ℝ≥0∞) Q) := hhalf
    _=2*μ ∞ (Q∩{z | ((q:ℝ≥0):ℝ≥0∞)<visitTime κ b z}) := by
      rw [stopped_strictPast_mass κ b μ hμ Q hQ hfin]
    _≤_ := by
      apply mul_le_mul_right
      apply measure_mono
      intro z hz
      exact ⟨hz.1,q,hqH',hz.2⟩

 

def rationalTestEnumeration : ℕ→ℚ≥0 := Classical.choose (exists_surjective_nat ℚ≥0)

lemma rationalTestEnumeration_surjective : Function.Surjective rationalTestEnumeration :=
  Classical.choose_spec (exists_surjective_nat ℚ≥0)

def rationalPastKernel (W : Measure GDriver) (a : ℝ)
    (μ : ℝ≥0∞→GDriver→Measure UpperPlane) (Q : Set UpperPlane) (H : ℝ≥0∞) :
    UpperPlane→ℝ≥0∞ :=
  countablePastKernel rationalTestEnumeration (fun q : ℚ≥0=>(q:ℝ≥0)) W a μ Q H

namespace TracePalmData
variable {κ a : ℝ} {W : Measure GDriver} {μ : ℝ≥0∞→GDriver→Measure UpperPlane}
    (D : TracePalmData κ a W μ)
include D

lemma rational_Palm (ha : 1/4<a) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (Q : Set UpperPlane) (hQ : IsCompact Q) (H : ℝ≥0∞) :
    (∫⁻b,μ ∞ b (Q∩{z | ∃q : ℚ≥0,H<μ ((q:ℝ≥0):ℝ≥0∞) b Q ∧
      ((q:ℝ≥0):ℝ≥0∞)<visitTime κ b z})∂W)=
      ∫⁻z in Q, ENNReal.ofReal (initialGreen a z)*rationalPastKernel W a μ Q H z∂upperArea :=
  D.countable_Palm ha hW rationalTestEnumeration (fun q : ℚ≥0=>(q:ℝ≥0))
    rationalTestEnumeration_surjective Q hQ H

lemma rational_kernel_measurable (ha : 1/4<a) [SFinite W]
    (Q : Set UpperPlane) (hQ : MeasurableSet Q) (H : ℝ≥0∞) :
    Measurable (rationalPastKernel W a μ Q H) :=
  D.countable_kernel_measurable ha rationalTestEnumeration (fun q : ℚ≥0=>(q:ℝ≥0)) Q hQ H

 

lemma expected_bad_mass_le (hκ : 0<κ) (ha : 1/4<a) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (Q : Set UpperPlane) (hQ : IsCompact Q) (H : ℝ) (hH : 0≤H) :
    (∫⁻b, {b | 2*ENNReal.ofReal H<μ ∞ b Q}.indicator (fun b=>μ ∞ b Q) b∂W) ≤
      2*∫⁻z in Q,ENNReal.ofReal (initialGreen a z)*
        rationalPastKernel W a μ Q (ENNReal.ofReal H) z∂upperArea := by
  have hm := D.countable_past_aemeasurable rationalTestEnumeration (fun q : ℚ≥0=>(q:ℝ≥0))
    rationalTestEnumeration_surjective Q hQ (ENNReal.ofReal H)
  rw [←D.rational_Palm ha hW Q hQ (ENNReal.ofReal H),←lintegral_const_mul'' _ hm]
  apply lintegral_mono_ae
  filter_upwards [D.path] with b hb
  by_cases hbad : 2*ENNReal.ofReal H<μ ∞ b Q
  · simp only [indicator,mem_ofPred_eq,ite_eq_left hbad]
    exact mass_le_twice_strict_past κ hκ b (fun v=>μ v b) hb Q hQ.measurableSet
      (D.compact_finite Q hQ ∞ b) H hH hbad
  · simp only [indicator,mem_ofPred_eq,ite_eq_right hbad]
    exact bot_le

end TracePalmData

end SLEExactGauge.PastMass
end
end

end OAI
