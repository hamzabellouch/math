import OAI.Analysis.NodalLength.AffineError

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function

namespace SharpNodal.Profiles
open Carleman

def regularWeight (ρ : ℝ) (x : Plane) : ℝ := ρ^2/(ρ^2+‖x‖^2)
def regularGradientWeight (ρ : ℝ) (x : Plane) : ℝ := (ρ+‖x‖)⁻¹

lemma continuous_regularWeight {ρ : ℝ} (hρ : 0<ρ) : Continuous (regularWeight ρ) := by
  unfold regularWeight
  fun_prop (disch := intro x; positivity)

lemma continuous_regularGradientWeight {ρ : ℝ} (hρ : 0<ρ) : Continuous (regularGradientWeight ρ) := by
  unfold regularGradientWeight
  fun_prop (disch := intro x; positivity)

lemma regularWeight_nonneg (ρ : ℝ) (x : Plane) : 0≤regularWeight ρ x := by
  unfold regularWeight
  positivity

lemma regularGradientWeight_nonneg {ρ : ℝ} (hρ : 0<ρ) (x : Plane) : 0≤regularGradientWeight ρ x := by
  unfold regularGradientWeight
  positivity

lemma regularWeight_integral {ρ T : ℝ} (hρ : 0<ρ) (hT : 0≤T) :
    (∫x in Metric.ball (0:Plane) T,regularWeight ρ x)=
      Real.pi*ρ^2*(Real.log (ρ^2+T^2)-Real.log (ρ^2)) := by
  simp only [regularWeight]
  rw [plane_radial_ball_integral (fun r => ρ^2/(ρ^2+r^2)) T]
  have hd (r : ℝ) : HasDerivAt (fun r : ℝ => (ρ^2/2)*Real.log (ρ^2+r^2))
      (r*(ρ^2/(ρ^2+r^2))) r := by
    have hr : ρ^2+r^2≠0 := ne_of_gt (by positivity)
    convert! ((((hasDerivAt_id r).pow 2).const_add (ρ^2)).log hr).const_mul (ρ^2/2) using 1
    simp only [id_eq,Pi.pow_apply,Nat.cast_ofNat,mul_one]
    field_simp
    ring
  have hc : Continuous (fun r : ℝ => r*(ρ^2/(ρ^2+r^2))) := by
    fun_prop (disch := intro r; positivity)
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) (hc.intervalIntegrable 0 T)]
  simp only [zero_pow (by norm_num : 2≠0),add_zero]
  ring

lemma regularWeight_integral_bound {ρ : ℝ} (hρ : 0<ρ) (hsmall : ρ≤1) :
    (∫x in Metric.ball (0:Plane) 6,regularWeight ρ x)≤
      Real.pi*ρ^2*(Real.log 37+2*|Real.log ρ|) := by
  rw [regularWeight_integral hρ (by norm_num)]
  have hs : ρ^2+(6:ℝ)^2≤37 := by nlinarith
  have hl := Real.log_le_log (show 0<ρ^2+(6:ℝ)^2 by positivity) hs
  rw [Real.log_pow]
  have hneg : Real.log ρ≤0 := Real.log_nonpos hρ.le hsmall
  rw [abs_of_nonpos hneg]
  exact mul_le_mul_of_nonneg_left (by norm_num at *; linarith) (by positivity)

lemma regularGradientWeight_integral_bound {ρ : ℝ} (hρ : 0<ρ) :
    (∫x in Metric.ball (0:Plane) 6,regularGradientWeight ρ x)≤12*Real.pi := by
  simp only [regularGradientWeight]
  rw [plane_radial_ball_integral (fun r => (ρ+r)⁻¹) 6]
  have hi : IntegrableOn (fun r : ℝ => r*(ρ+r)⁻¹) (Ioo 0 6) := by
    apply ((continuousOn_id.mul ((continuousOn_const.add continuousOn_id).inv₀ (fun r hr => ?_))).integrableOn_Icc).mono_set Ioo_subset_Icc_self
    change ρ+r≠0
    exact ne_of_gt (by linarith [hr.1])
  have hle : (∫r in Ioo (0:ℝ) 6,r*(ρ+r)⁻¹)≤6 := by
    calc
      _ ≤ ∫_r in Ioo (0:ℝ) 6,(1:ℝ) := by
        apply setIntegral_mono_on hi (integrableOn_const (by simp)) measurableSet_Ioo
        intro r hr
        rw [← div_eq_mul_inv,div_le_iff₀ (by linarith [hr.1] : 0<ρ+r)]
        linarith
      _ = 6 := by norm_num
  nlinarith [mul_le_mul_of_nonneg_left hle (show 0≤2*Real.pi by positivity)]

lemma translated_kernel_integral_le {f : Plane → ℝ} (hf : Continuous f)
    (hpos : ∀x,0≤f x) {R S : ℝ} {z : Plane} (hz : ‖z‖<S) :
    (∫x in Metric.ball (0:Plane) R,f (x-z))≤∫x in Metric.ball (0:Plane) (R+S),f x := by
  let F := (Metric.ball (0:Plane) (R+S)).indicator f
  have hi : Integrable F :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0:Plane) (R+S))).mono_set Metric.ball_subset_closedBall |>.integrable_indicator measurableSet_ball
  have hit : Integrable (fun x : Plane => F (x-z)) :=
    (measurePreserving_sub_right volume z).integrable_comp hi.aestronglyMeasurable |>.mpr hi
  have he (x : Plane) (hx : x∈Metric.ball (0:Plane) R) : f (x-z)=F (x-z) := by
    have hn : ‖x-z‖<R+S := (norm_sub_le x z).trans_lt (add_lt_add (by simpa only [Metric.mem_ball,dist_zero_right] using hx) hz)
    exact (indicator_of_mem (show x-z∈Metric.ball (0:Plane) (R+S) by simpa only [Metric.mem_ball,dist_zero_right] using hn) f).symm
  calc
    _ = ∫x in Metric.ball (0:Plane) R,F (x-z) := setIntegral_congr_fun measurableSet_ball he
    _ ≤ ∫x,F (x-z) := integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun x => indicator_nonneg (fun x _ => hpos x) _)) hit
    _ = ∫x,F x := integral_sub_right_eq_self F z
    _ = _ := integral_indicator measurableSet_ball

lemma separated_disks {Y : Finset Plane} {ρ : ℝ} (hρ : 0<ρ)
    (hsep : ∀y∈Y,∀y'∈Y,y≠y' → ρ≤‖y-y'‖) :
    Set.Pairwise (Y:Set Plane) (Disjoint on (fun y => Metric.ball y (ρ/3))) := by
  intro y hy y' hy' hne
  apply Metric.ball_disjoint_ball
  have hs := hsep y hy y' hy' hne
  rw [dist_eq_norm]
  linarith

lemma separated_centers_integral_bound {Y : Finset Plane} {ρ : ℝ} (hρ : 0<ρ) (hsmall : ρ≤1)
    (hcenters : ∀y∈Y,‖y‖≤1) (hsep : ∀y∈Y,∀y'∈Y,y≠y' → ρ≤‖y-y'‖)
    {f : Plane → ℝ} (hf : Continuous f) (hpos : ∀x,0≤f x)
    {a : Plane → ℝ} (hlocal : ∀y∈Y,∀x∈Metric.ball y (ρ/3),a y≤f x) :
    Real.pi*(ρ/3)^2*(∑y∈Y,a y)≤∫x in Metric.ball (0:Plane) 2,f x := by
  classical
  have hi : IntegrableOn f (Metric.ball (0:Plane) 2) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0:Plane) 2)).mono_set Metric.ball_subset_closedBall
  have hsub (y : Plane) (hy : y∈Y) : Metric.ball y (ρ/3)⊆Metric.ball (0:Plane) 2 := by
    intro x hx
    have hx' : ‖x-y‖<ρ/3 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    have hh := norm_add_le (x-y) y
    rw [sub_add_cancel] at hh
    simp only [Metric.mem_ball,dist_zero_right]
    linarith [hcenters y hy]
  calc
    _ = ∑y∈Y,(∫_x in Metric.ball y (ρ/3),a y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      rw [integral_const,Measure.real,Measure.restrict_apply_univ,EuclideanSpace.volume_ball_fin_two]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (show 0≤ρ/3 by positivity), ENNReal.toReal_ofReal Real.pi_pos.le,smul_eq_mul]
      ring
    _ ≤ ∑y∈Y,(∫x in Metric.ball y (ρ/3),f x) := by
      apply Finset.sum_le_sum
      intro y hy
      apply setIntegral_mono_on (integrableOn_const measure_ball_ne_top) (hi.mono_set (hsub y hy)) measurableSet_ball
      exact hlocal y hy
    _ = ∫x in ⋃y∈Y,Metric.ball y (ρ/3),f x :=
      (integral_biUnion_finset Y (fun _ _ => measurableSet_ball) (separated_disks hρ hsep) (fun y hy => hi.mono_set (hsub y hy))).symm
    _ ≤ ∫x in Metric.ball (0:Plane) 2,f x := by
      apply integral_mono_measure (Measure.restrict_mono (by simpa only [iUnion_subset_iff] using hsub) (le_refl volume))
        (Eventually.of_forall hpos) hi

lemma regularWeight_center_comparison {ρ : ℝ} (hρ : 0<ρ) {x y z : Plane}
    (hxy : ‖x-y‖<ρ/3) : regularWeight ρ (y-z)≤4*regularWeight ρ (x-z) := by
  have ht : ‖x-z‖≤‖y-z‖+ρ := by
    have hh := norm_add_le (x-y) (y-z)
    rw [sub_add_sub_cancel] at hh
    linarith
  have hs := mul_self_le_mul_self (norm_nonneg (x-z)) ht
  have hd : ρ^2+‖x-z‖^2≤4*(ρ^2+‖y-z‖^2) := by
    nlinarith [sq_nonneg (‖y-z‖-ρ)]
  unfold regularWeight
  rw [div_le_iff₀ (show 0<ρ^2+‖y-z‖^2 by positivity)]
  rw [← mul_div_assoc,div_mul_eq_mul_div,le_div_iff₀ (show 0<ρ^2+‖x-z‖^2 by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hd (sq_nonneg ρ)]

lemma regularGradientWeight_center_comparison {ρ : ℝ} (hρ : 0<ρ) {x y z : Plane}
    (hxy : ‖x-y‖<ρ/3) : regularGradientWeight ρ (y-z)≤2*regularGradientWeight ρ (x-z) := by
  have ht : ‖x-z‖≤‖y-z‖+ρ := by
    have hh := norm_add_le (x-y) (y-z)
    rw [sub_add_sub_cancel] at hh
    linarith
  unfold regularGradientWeight
  rw [← one_div,← div_eq_mul_inv,div_le_div_iff₀ (by positivity) (by positivity)]
  linarith [norm_nonneg (y-z)]

lemma separated_regularWeight_sum {Y : Finset Plane} {ρ : ℝ} (hρ : 0<ρ) (hsmall : ρ≤1)
    (hcenters : ∀y∈Y,‖y‖≤1) (hsep : ∀y∈Y,∀y'∈Y,y≠y' → ρ≤‖y-y'‖)
    {z : Plane} (hz : ‖z‖<4) :
    ρ^2*(∑y∈Y,regularWeight ρ (y-z))≤36*ρ^2*(Real.log 37+2*|Real.log ρ|) := by
  have hb := separated_centers_integral_bound hρ hsmall hcenters hsep
    (f:=fun x =>4*regularWeight ρ (x-z))
    (continuous_const.mul ((continuous_regularWeight hρ).comp (continuous_id.sub continuous_const)))
    (fun x => mul_nonneg (by norm_num) (regularWeight_nonneg ρ (x-z)))
    (a:=fun y =>regularWeight ρ (y-z))
    (fun y _ x hx => regularWeight_center_comparison hρ (by simpa only [Metric.mem_ball,dist_eq_norm] using hx))
  rw [integral_const_mul] at hb
  have ht := translated_kernel_integral_le (continuous_regularWeight hρ)
    (regularWeight_nonneg ρ) (R:=2) hz
  have hr := regularWeight_integral_bound hρ hsmall
  norm_num at ht
  have h := hb.trans (mul_le_mul_of_nonneg_left (ht.trans hr) (by norm_num : (0:ℝ)≤4))
  have hp := Real.pi_pos
  nlinarith

lemma separated_regularGradientWeight_sum {Y : Finset Plane} {ρ : ℝ} (hρ : 0<ρ) (hsmall : ρ≤1)
    (hcenters : ∀y∈Y,‖y‖≤1) (hsep : ∀y∈Y,∀y'∈Y,y≠y' → ρ≤‖y-y'‖)
    {z : Plane} (hz : ‖z‖<4) :
    ρ^2*(∑y∈Y,regularGradientWeight ρ (y-z))≤216 := by
  have hb := separated_centers_integral_bound hρ hsmall hcenters hsep
    (f:=fun x =>2*regularGradientWeight ρ (x-z))
    (continuous_const.mul ((continuous_regularGradientWeight hρ).comp (continuous_id.sub continuous_const)))
    (fun x => mul_nonneg (by norm_num) (regularGradientWeight_nonneg hρ (x-z)))
    (a:=fun y =>regularGradientWeight ρ (y-z))
    (fun y _ x hx => regularGradientWeight_center_comparison hρ (by simpa only [Metric.mem_ball,dist_eq_norm] using hx))
  rw [integral_const_mul] at hb
  have ht := translated_kernel_integral_le (continuous_regularGradientWeight hρ)
    (regularGradientWeight_nonneg hρ) (R:=2) hz
  have hr := regularGradientWeight_integral_bound hρ
  norm_num at ht
  have h := hb.trans (mul_le_mul_of_nonneg_left (ht.trans hr) (by norm_num : (0:ℝ)≤2))
  have hp := Real.pi_pos
  nlinarith

lemma farWeight_le_regularWeight {R ρ : ℝ} (hR : 1≤R) (hρ : 0<ρ) (y z : Plane) :
    farWeight R ρ y z≤(1+4*R^2)*regularWeight ρ (y-z) := by
  unfold farWeight regularWeight
  split_ifs with hd
  · have hdpos : 0<‖y-z‖ := lt_trans (by positivity) hd
    have hρd : ρ≤‖y-z‖ := by nlinarith
    rw [div_le_iff₀ (by positivity),← mul_div_assoc,div_mul_eq_mul_div,
      le_div_iff₀ (by positivity)]
    have hs : ρ^2≤‖y-z‖^2 := pow_le_pow_left₀ hρ.le hρd 2
    have hRR := mul_le_mul_of_nonneg_right (show 1≤R^2 by nlinarith) (sq_nonneg ‖y-z‖)
    nlinarith [hRR, mul_nonneg (sq_nonneg ρ) (show 0≤(1+4*R^2)*‖y-z‖^2-(ρ^2+‖y-z‖^2) by nlinarith [hRR])]
  · have hd' : ‖y-z‖≤2*R*ρ := le_of_not_gt hd
    rw [← mul_div_assoc,le_div_iff₀ (by positivity)]
    have hs := pow_le_pow_left₀ (norm_nonneg (y-z)) hd' 2
    nlinarith

lemma farGradient_le_regularGradientWeight {R ρ : ℝ} (hR : 1≤R) (hρ : 0<ρ) (y z : Plane) :
    ‖farGradient R ρ y z‖≤2*regularGradientWeight ρ (y-z) := by
  unfold farGradient regularGradientWeight
  split_ifs with hd
  · have hdpos : 0<‖y-z‖ := lt_trans (by positivity) hd
    have hρd : ρ≤‖y-z‖ := by nlinarith
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have he : (‖y-z‖^2)⁻¹*‖y-z‖=(‖y-z‖)⁻¹ := by field_simp
    rw [he,← one_div,← div_eq_mul_inv,div_le_div_iff₀ hdpos (by positivity)]
    linarith
  · simp only [norm_zero]
    positivity

lemma separated_farWeight_sum {Y : Finset Plane} {R ρ : ℝ} (hR : 1≤R) (hρ : 0<ρ) (hsmall : ρ≤1)
    (hcenters : ∀y∈Y,‖y‖≤1) (hsep : ∀y∈Y,∀y'∈Y,y≠y' → ρ≤‖y-y'‖)
    {z : Plane} (hz : ‖z‖<4) :
    ρ^2*(∑y∈Y,farWeight R ρ y z)≤36*(1+4*R^2)*ρ^2*(Real.log 37+2*|Real.log ρ|) := by
  calc
    _ ≤ ρ^2*(∑y∈Y,(1+4*R^2)*regularWeight ρ (y-z)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ =>farWeight_le_regularWeight hR hρ y z)) (sq_nonneg ρ)
    _ = (1+4*R^2)*(ρ^2*(∑y∈Y,regularWeight ρ (y-z))) := by rw [← Finset.mul_sum]; ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (separated_regularWeight_sum hρ hsmall hcenters hsep hz)
        (show 0≤1+4*R^2 by positivity)
      nlinarith

lemma separated_farGradient_sum {Y : Finset Plane} {R ρ : ℝ} (hR : 1≤R) (hρ : 0<ρ) (hsmall : ρ≤1)
    (hcenters : ∀y∈Y,‖y‖≤1) (hsep : ∀y∈Y,∀y'∈Y,y≠y' → ρ≤‖y-y'‖)
    {z : Plane} (hz : ‖z‖<4) :
    ρ^2*(∑y∈Y,‖farGradient R ρ y z‖)≤432 := by
  calc
    _ ≤ ρ^2*(∑y∈Y,2*regularGradientWeight ρ (y-z)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ =>farGradient_le_regularGradientWeight hR hρ y z)) (sq_nonneg ρ)
    _ = 2*(ρ^2*(∑y∈Y,regularGradientWeight ρ (y-z))) := by rw [← Finset.mul_sum]; ring
    _ ≤ _ := by nlinarith [separated_regularGradientWeight_sum hρ hsmall hcenters hsep hz]

lemma separated_farWeight_integrals {Y : Finset Plane} {R ρ : ℝ} (hR : 1≤R) (hρ : 0<ρ) (hsmall : ρ≤1)
    (hcenters : ∀y∈Y,‖y‖≤1) (hsep : ∀y∈Y,∀y'∈Y,y≠y' → ρ≤‖y-y'‖)
    (ν : Measure Plane) [IsFiniteMeasure ν] (hs : ∀ᵐz ∂ν,‖z‖<4) :
    ρ^2*(∑y∈Y,∫z,farWeight R ρ y z ∂ν)≤
      36*(1+4*R^2)*ν.real univ*ρ^2*(Real.log 37+2*|Real.log ρ|) := by
  rw [← integral_finsetSum Y (fun y _ => integrable_farWeight ν hR hρ y),← integral_const_mul]
  have hi := (integrable_finsetSum Y (fun y _ => integrable_farWeight ν hR hρ y)).const_mul (ρ^2)
  have hh := integral_mono_ae hi (integrable_const (36*(1+4*R^2)*ρ^2*(Real.log 37+2*|Real.log ρ|)))
    (hs.mono (fun z hz =>separated_farWeight_sum hR hρ hsmall hcenters hsep hz))
  rw [integral_const,smul_eq_mul] at hh
  nlinarith

lemma separated_farGradient_integrals {Y : Finset Plane} {R ρ : ℝ} (hR : 1≤R) (hρ : 0<ρ) (hsmall : ρ≤1)
    (hcenters : ∀y∈Y,‖y‖≤1) (hsep : ∀y∈Y,∀y'∈Y,y≠y' → ρ≤‖y-y'‖)
    (ν : Measure Plane) [IsFiniteMeasure ν] (hs : ∀ᵐz ∂ν,‖z‖<4) :
    ρ^2*(∑y∈Y,‖∫z,farGradient R ρ y z ∂ν‖)≤432*ν.real univ := by
  calc
    _ ≤ ρ^2*(∑y∈Y,∫z,‖farGradient R ρ y z‖ ∂ν) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ =>norm_integral_le_integral_norm _)) (sq_nonneg ρ)
    _ = ∫z,ρ^2*(∑y∈Y,‖farGradient R ρ y z‖) ∂ν := by
      rw [integral_const_mul,integral_finsetSum Y (fun y _ =>(integrable_farGradient ν (by linarith) hρ y).norm)]
    _ ≤ ∫_z,(432:ℝ) ∂ν := by
      apply integral_mono_ae ((integrable_finsetSum Y (fun y _ =>(integrable_farGradient ν (by linarith) hρ y).norm)).const_mul (ρ^2)) (integrable_const _)
      exact hs.mono (fun z hz =>separated_farGradient_sum hR hρ hsmall hcenters hsep hz)
    _ = _ := by rw [integral_const,smul_eq_mul]; ring

theorem affine_profile_grid : ∃Cs Ce : ℝ,0≤Cs ∧ 0≤Ce ∧ ∀V : Plane → EReal,
    UpperSemicontinuousOn V (Metric.ball 0 1000) →
    (∀x∈Metric.ball (0:Plane) 1000,V x≤0) → FullTestProperty (Metric.ball 0 1000) V →
    (∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a) →
    ∀ρ : ℝ,0<ρ → 2000*ρ≤1 → ∀Y : Finset Plane,
    (∀y∈Y,‖y‖≤1) → (∀y∈Y,∀y'∈Y,y≠y' → ρ≤‖y-y'‖) →
    ρ^2*(Y.card:ℝ)=1 →
    ∃(L : Plane → Plane →L[ℝ] ℝ) (e : Plane → ℝ),
      (∀y∈Y,0≤e y) ∧
      (∀y∈Y,(⨆x∈Metric.closedBall y (1000*ρ),V x-(L y (x-y):EReal))≤
        (⨆x∈Metric.ball y ρ,V x-(L y (x-y):EReal))+(e y:EReal)) ∧
      ρ^2*(∑y∈Y,‖L y‖)≤Cs ∧
      ρ^2*(∑y∈Y,e y)≤Ce*ρ^2*(1+|Real.log ρ|) := by
  obtain ⟨Ch,hCh,hdec⟩ := profile_ae_decomposition_uniform
  obtain ⟨Ck,hCk,hcomp⟩ := potential_profile_affine_sup_bound (R:=1000) (by norm_num)
  let Dh := 4*Ch*((2*1000:ℝ)^2+1)
  let Dp := Ck*36*(1+4*(2*1000:ℝ)^2)*Ch
  have hDh : 0≤Dh := by dsimp [Dh]; positivity
  have hDp : 0≤Dp := by dsimp [Dp]; positivity
  refine ⟨434*Ch,Dh+Dp*(|Real.log 37|+2),by positivity,by positivity,?_⟩
  intro V hV hneg htest hanchor ρ hρ hsmall Y hcenters hsep hcard
  have hρsmall : ρ≤1 := by linarith
  obtain ⟨ν,hν,hs,hmass,h,hh,_hharm,heq,hderiv⟩ := hdec V hV hneg htest hanchor
  let := hν
  let L := fun y =>fderiv ℝ h y+innerSL ℝ (∫z,farGradient (2*1000) ρ y z ∂ν)
  let e := fun y =>Dh*ρ^2+Ck*(∫z,farWeight (2*1000) ρ y z ∂ν)
  refine ⟨L,e,?_,?_,?_,?_⟩
  · intro y _hy
    dsimp [e]
    exact add_nonneg (mul_nonneg hDh (sq_nonneg ρ)) (mul_nonneg hCk
      (integral_nonneg (fun z =>(farWeight_bounds (by norm_num) hρ y z).1)))
  · intro y hy
    exact hcomp ν hs V h hV hneg htest hanchor hh heq Ch hCh
      (fun z i j =>(hderiv z).2 i j) ρ hρ y (hcenters y hy) (by simpa only [show (2*1000:ℝ)=2000 by norm_num] using hsmall)
  · have hL (y : Plane) : ‖L y‖≤2*Ch+‖∫z,farGradient (2*1000) ρ y z ∂ν‖ := by
      dsimp [L]
      exact (norm_add_le _ _).trans (by rw [innerSL_apply_norm]; exact add_le_add (fderiv_norm_le_two hCh y (hderiv y).1) le_rfl)
    have hslope := separated_farGradient_integrals (R:=2*1000) (by norm_num) hρ hρsmall hcenters hsep ν hs
    calc
      _ ≤ ρ^2*(∑y∈Y,(2*Ch+‖∫z,farGradient (2*1000) ρ y z ∂ν‖)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ =>hL y)) (sq_nonneg ρ)
      _ = 2*Ch+ρ^2*(∑y∈Y,‖∫z,farGradient (2*1000) ρ y z ∂ν‖) := by
        rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_add]
        rw [← mul_assoc,hcard,one_mul]
      _ ≤ _ := by nlinarith
  · have heint := separated_farWeight_integrals (R:=2*1000) (by norm_num) hρ hρsmall hcenters hsep ν hs
    have hlog : 0≤Real.log 37+2*|Real.log ρ| := by positivity
    have hb : ρ^2*(∑y∈Y,e y)≤Dh*ρ^2+Dp*ρ^2*(Real.log 37+2*|Real.log ρ|) := by
      dsimp only [e]
      rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum,mul_add]
      have hc : ρ^2*((Y.card:ℝ)*(Dh*ρ^2))=Dh*ρ^2 := by rw [← mul_assoc,hcard,one_mul]
      rw [hc]
      have hm := mul_le_mul_of_nonneg_right hmass
        (show 0≤36*(1+4*(2*1000:ℝ)^2)*ρ^2*(Real.log 37+2*|Real.log ρ|) by positivity)
      have hh' := mul_le_mul_of_nonneg_left heint hCk
      dsimp [Dp]
      nlinarith
    have hlast : Dh*ρ^2+Dp*ρ^2*(Real.log 37+2*|Real.log ρ|)≤
        (Dh+Dp*(|Real.log 37|+2))*ρ^2*(1+|Real.log ρ|) := by
      have hl := le_abs_self (Real.log 37)
      have he : Real.log 37+2*|Real.log ρ|≤(|Real.log 37|+2)*(1+|Real.log ρ|) := by
        nlinarith [mul_nonneg (abs_nonneg (Real.log 37)) (abs_nonneg (Real.log ρ))]
      have hp := mul_le_mul_of_nonneg_left he (mul_nonneg hDp (sq_nonneg ρ))
      nlinarith [mul_nonneg (mul_nonneg hDh (sq_nonneg ρ)) (abs_nonneg (Real.log ρ))]
    exact hb.trans hlast

end SharpNodal.Profiles

end

end OAI
