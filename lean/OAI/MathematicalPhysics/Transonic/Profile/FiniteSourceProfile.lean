import OAI.MathematicalPhysics.Transonic.Profile.SourceParameters
import OAI.MathematicalPhysics.Transonic.Profile.PhysicalProfile
import OAI.MathematicalPhysics.Transonic.Shooting.FiniteProfile

namespace OAI

section
noncomputable section
namespace SepticProfile.SonicShooting
open Set Filter SourceFamily AxisBarriers
open scoped Topology ContDiff

def MatchedPair.beta (M : MatchedPair) : ℝ := ShootingParameters.beta M.parameter.val
def MatchedPair.radius (M : MatchedPair) : ℝ := sonicRadius M.beta
def MatchedPair.sonicU (M : MatchedPair) (y : ℝ) : ℝ := sonicSpeed*M.localProfile (y/M.radius)
def MatchedPair.velocity (M : MatchedPair) (y : ℝ) : ℝ := velocityToU y (M.sonicU y)

lemma MatchedPair.beta_bounds (M : MatchedPair) : 1<M.beta ∧ M.beta*(ell+Real.sqrt ell)<3 :=
  ShootingParameters.standing_beta_bound M.parameter.property
lemma MatchedPair.radius_bounds (M : MatchedPair) : 0<M.radius ∧ M.radius<1 := by
  have h := source_parameter_bounds M.beta_bounds.1 M.beta_bounds.2
  exact ⟨h.2.2.2.2.1,h.2.2.2.2.2.1⟩
lemma sonicSpeed_bounds : 0<sonicSpeed ∧ sonicSpeed<1 := by
  have hp : 0<sonicSpeed := by unfold sonicSpeed ell;positivity
  refine ⟨hp,?_⟩
  nlinarith [sonicSpeed_sq]

lemma MatchedPair.local_zero (M : MatchedPair) : M.localProfile 0=0 := by
  rw [(M.local_eventually_inner (by linarith [(endRadius_bounds M.sonic.e_pos M.sonic.e_lt).1] : 0<endRadius M.sonic.e)).eq_of_nhds,
    (M.inner_eventually_axis M.axis.δ_pos).eq_of_nhds]
  simp only [MatchedPair.axisGerm,AxisFamily.UniformGerm.velocity,zero_mul]

lemma MatchedPair.sonicU_smooth (M : MatchedPair) {y : ℝ}
    (hy : y/M.radius ∈ Icc (0:ℝ) (1+M.sonic.width)) : ContDiffAt ℝ ∞ M.sonicU y := by
  exact contDiffAt_const.mul ((M.local_smooth_at hy).comp y (contDiffAt_id.div_const M.radius))

lemma MatchedPair.sonicU_derivative (M : MatchedPair) {y : ℝ}
    (hy : y/M.radius ∈ Icc (0:ℝ) (1+M.sonic.width)) :
    HasDerivAt M.sonicU (SepticProfile.q M.beta/3*deriv M.localProfile (y/M.radius)) y := by
  have hd := ((M.local_smooth_at hy).differentiableAt (by norm_num)).hasDerivAt
  have h := (hd.comp (h:=fun x : ℝ => x/M.radius) y ((hasDerivAt_id y).div_const M.radius)).const_mul sonicSpeed
  apply h.congr_deriv
  have hr : M.radius=3*sonicSpeed/SepticProfile.q M.beta := sonicRadius_eq M.beta
  have hq : SepticProfile.q M.beta≠0 := ne_of_gt (source_q_pos M.parameter)
  have hc : sonicSpeed≠0 := ne_of_gt sonicSpeed_bounds.1
  rw [hr]
  field_simp

lemma MatchedPair.sonicU_equation (M : MatchedPair) {y : ℝ}
    (hy : y/M.radius ∈ Icc (0:ℝ) (1+M.sonic.width)) :
    sonicDenom ell y (M.sonicU y)*deriv M.sonicU y=sonicNumer ell M.beta y (M.sonicU y) := by
  have he := M.local_equation hy
  have hp : normalizedDenom M.beta (y/M.radius) (M.localProfile (y/M.radius))*deriv M.localProfile (y/M.radius)=
      normalizedNumer M.beta (y/M.radius) (M.localProfile (y/M.radius)) := by
    simpa only [normalizedDenom,normalizedNumer,MatchedPair.beta,source_sigma,source_kappa,AxisBarriers.D,AxisBarriers.N] using he
  have ht := (normalized_equation_iff (ne_of_gt (source_q_pos M.parameter))
    (y/M.radius) (M.localProfile (y/M.radius)) (deriv M.localProfile (y/M.radius))).mpr hp
  have hr : sonicRadius M.beta*(y/M.radius)=y := by
    change M.radius*(y/M.radius)=y
    exact mul_div_cancel₀ y (ne_of_gt M.radius_bounds.1)
  change sonicDenom ell (sonicRadius M.beta*(y/M.radius)) (M.sonicU y)*
    (SepticProfile.q M.beta/3*deriv M.localProfile (y/M.radius))=
    sonicNumer ell M.beta (sonicRadius M.beta*(y/M.radius)) (M.sonicU y) at ht
  rw [hr,← (M.sonicU_derivative hy).deriv] at ht
  exact ht

lemma MatchedPair.sonicU_zero (M : MatchedPair) : M.sonicU 0=0 := by
  simp only [MatchedPair.sonicU,zero_div,M.local_zero,mul_zero]
lemma MatchedPair.sonicU_at_radius (M : MatchedPair) : M.sonicU M.radius=sonicSpeed := by
  simp only [MatchedPair.sonicU,div_self (ne_of_gt M.radius_bounds.1),M.local_value,mul_one]

lemma MatchedPair.exists_physical_width (M : MatchedPair) : ∃ w : ℝ,
    0<w ∧ w≤M.sonic.width ∧ M.radius*(1+w)<1 ∧
      ∀ z ∈ Icc (0:ℝ) (1+w), |sonicSpeed*M.localProfile z|<1 := by
  have hs := (M.local_smooth_at (show (1:ℝ) ∈ Icc (0:ℝ) (1+M.sonic.width) from
    ⟨by norm_num,by linarith [M.sonic.width_pos]⟩)).continuousAt
  have hc : ContinuousAt (fun z => |sonicSpeed*M.localProfile z|) 1 :=
    (continuousAt_const.mul hs).abs
  have hn : ∀ᶠ z in 𝓝 (1:ℝ), |sonicSpeed*M.localProfile z|<1 := by
    apply hc.eventually (Iio_mem_nhds _)
    simpa only [M.local_value,mul_one,abs_of_pos sonicSpeed_bounds.1] using sonicSpeed_bounds.2
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
  let w := min M.sonic.width (min (ε/2) ((1/M.radius-1)/2))
  have hw : 0<w := by
    apply lt_min M.sonic.width_pos
    apply lt_min (by linarith)
    have hdiv : 1<1/M.radius := (one_lt_div M.radius_bounds.1).mpr M.radius_bounds.2
    linarith
  refine ⟨w,hw,min_le_left _ _,?_,?_⟩
  · have hh : w≤(1/M.radius-1)/2 := (min_le_right _ _).trans (min_le_right _ _)
    have hd : M.radius*(1/M.radius)=1 := mul_div_cancel₀ 1 (ne_of_gt M.radius_bounds.1)
    nlinarith [mul_le_mul_of_nonneg_left hh M.radius_bounds.1.le,M.radius_bounds.2]
  · intro z hz
    by_cases hl : z<1
    · by_cases hz0 : z=0
      · simp only [hz0,M.local_zero,mul_zero,abs_zero];norm_num
      · have hu := M.local_range ⟨lt_of_le_of_ne hz.1 (Ne.symm hz0),hl⟩
        rw [abs_of_pos (mul_pos sonicSpeed_bounds.1 hu.1)]
        exact (mul_lt_mul_of_pos_left hu.2 sonicSpeed_bounds.1).trans (by simpa using sonicSpeed_bounds.2)
    · apply hball
      rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hl))]
      have hh : w≤ε/2 := (min_le_right _ _).trans (min_le_left _ _)
      linarith [hz.2]

structure PhysicalWidth (M : MatchedPair) where
  w : ℝ
  pos : 0<w
  le_width : w≤M.sonic.width
  end_lt : M.radius*(1+w)<1
  range : ∀ z ∈ Icc (0:ℝ) (1+w), |sonicSpeed*M.localProfile z|<1

lemma MatchedPair.exists_physicalWidth (M : MatchedPair) : Nonempty (PhysicalWidth M) := by
  obtain ⟨w,hp,hl,he,hr⟩ := M.exists_physical_width
  exact ⟨⟨w,hp,hl,he,hr⟩⟩

def PhysicalWidth.endpoint {M : MatchedPair} (W : PhysicalWidth M) : ℝ := M.radius*(1+W.w)

lemma PhysicalWidth.endpoint_bounds {M : MatchedPair} (W : PhysicalWidth M) :
    M.radius<W.endpoint ∧ W.endpoint<1 := by
  refine ⟨?_,W.end_lt⟩
  unfold PhysicalWidth.endpoint
  nlinarith [mul_pos M.radius_bounds.1 W.pos]

lemma PhysicalWidth.rescale {M : MatchedPair} (W : PhysicalWidth M) {y : ℝ}
    (hy : y ∈ Icc (0:ℝ) W.endpoint) : y/M.radius ∈ Icc (0:ℝ) (1+W.w) := by
  exact ⟨div_nonneg hy.1 M.radius_bounds.1.le,
    (div_le_iff₀ M.radius_bounds.1).mpr (by simpa only [PhysicalWidth.endpoint,mul_comm] using hy.2)⟩
lemma PhysicalWidth.rescale_full {M : MatchedPair} (W : PhysicalWidth M) {y : ℝ}
    (hy : y ∈ Icc (0:ℝ) W.endpoint) : y/M.radius ∈ Icc (0:ℝ) (1+M.sonic.width) :=
  ⟨(W.rescale hy).1,(W.rescale hy).2.trans (by linarith [W.le_width])⟩
lemma PhysicalWidth.y_abs {M : MatchedPair} (W : PhysicalWidth M) {y : ℝ}
    (hy : y ∈ Icc (0:ℝ) W.endpoint) : |y|<1 := by
  rw [abs_of_nonneg hy.1]
  exact hy.2.trans_lt W.end_lt
lemma PhysicalWidth.U_abs {M : MatchedPair} (W : PhysicalWidth M) {y : ℝ}
    (hy : y ∈ Icc (0:ℝ) W.endpoint) : |M.sonicU y|<1 := W.range _ (W.rescale hy)
lemma PhysicalWidth.chart_pos {M : MatchedPair} (W : PhysicalWidth M) {y : ℝ}
    (hy : y ∈ Icc (0:ℝ) W.endpoint) : 0<1-y*M.sonicU y := by
  have hu := (abs_lt.mp (W.U_abs hy)).2
  have hy1 : y<1 := hy.2.trans_lt W.end_lt
  have hm : y*M.sonicU y≤y := by nlinarith [mul_nonneg hy.1 (sub_nonneg.mpr hu.le)]
  linarith

lemma PhysicalWidth.velocity_smooth {M : MatchedPair} (W : PhysicalWidth M) {y : ℝ}
    (hy : y ∈ Icc (0:ℝ) W.endpoint) : ContDiffAt ℝ ∞ M.velocity y := by
  have hU := M.sonicU_smooth (W.rescale_full hy)
  exact (contDiffAt_id.sub hU).div (contDiffAt_const.sub (contDiffAt_id.mul hU))
    (ne_of_gt (W.chart_pos hy))

lemma PhysicalWidth.velocity_equation {M : MatchedPair} (W : PhysicalWidth M) {y : ℝ}
    (hy : y ∈ Icc (0:ℝ) W.endpoint) :
    profileDenom ell y (M.velocity y)*deriv M.velocity y=profileNumer ell M.beta y (M.velocity y) := by
  have hu := ((M.sonicU_smooth (W.rescale_full hy)).differentiableAt (by norm_num)).hasDerivAt
  have hv := hasDerivAt_velocityToU hu (ne_of_gt (W.chart_pos hy))
  change HasDerivAt M.velocity _ y at hv
  rw [hv.deriv]
  exact inverse_profile_equation (ne_of_gt (W.chart_pos hy)) (M.sonicU_equation (W.rescale_full hy))

lemma PhysicalWidth.velocity_abs {M : MatchedPair} (W : PhysicalWidth M) {y : ℝ}
    (hy : y ∈ Icc (0:ℝ) W.endpoint) : |M.velocity y|<1 :=
  velocityToU_range (W.y_abs hy) (W.U_abs hy)

lemma MatchedPair.local_positive (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Ioc (0:ℝ) (1+M.sonic.width)) : 0<M.localProfile z := by
  rcases lt_trichotomy z 1 with hl|he|hr
  · exact (M.local_range ⟨hz.1,hl⟩).1
  · simp only [he,M.local_value];norm_num
  · have hE : endRadius M.sonic.e<z := (endRadius_bounds M.sonic.e_pos M.sonic.e_lt).2.trans hr
    rw [(M.local_eventually_germ hE).eq_of_nhds]
    linarith [M.sonic.germArc_above M.parameter ⟨hr,hz.2⟩]

lemma PhysicalWidth.velocity_below {M : MatchedPair} (W : PhysicalWidth M) {y : ℝ}
    (hy : y ∈ Ioc (0:ℝ) W.endpoint) : M.velocity y<y ∧ y*M.velocity y<1 := by
  have hu : 0<M.sonicU y := mul_pos sonicSpeed_bounds.1
    (M.local_positive ⟨div_pos hy.1 M.radius_bounds.1,(W.rescale_full ⟨hy.1.le,hy.2⟩).2⟩)
  refine ⟨velocityToU_below (W.y_abs ⟨hy.1.le,hy.2⟩) hu (W.chart_pos ⟨hy.1.le,hy.2⟩),?_⟩
  have hv := (abs_lt.mp (W.velocity_abs ⟨hy.1.le,hy.2⟩)).2
  have hy1 : y<1 := hy.2.trans_lt W.end_lt
  nlinarith [mul_pos hy.1 (sub_pos.mpr hv)]

lemma PhysicalWidth.recover_U {M : MatchedPair} (W : PhysicalWidth M) {y : ℝ}
    (hy : y ∈ Icc (0:ℝ) W.endpoint) : velocityToU y (M.velocity y)=M.sonicU y := by
  apply velocityToU_involutive _ (ne_of_gt (W.chart_pos hy))
  have hh := W.y_abs hy
  have hp : 0<1-y^2 := by nlinarith [(abs_lt.mp hh).1,(abs_lt.mp hh).2]
  exact ne_of_gt hp

lemma PhysicalWidth.unique_sonic {M : MatchedPair} (W : PhysicalWidth M) {y : ℝ}
    (hy : y ∈ Icc (0:ℝ) W.endpoint) :
    velocityToU y (M.velocity y)=sonicSpeed ↔ y=M.radius := by
  rw [W.recover_U hy]
  by_cases hz : y=0
  · simp only [hz,M.sonicU_zero]
    constructor
    · intro h;linarith [sonicSpeed_bounds.1]
    · intro h;linarith [M.radius_bounds.1]
  · have hl : 0<y := lt_of_le_of_ne hy.1 (Ne.symm hz)
    have hh := M.local_unique_sonic ⟨div_pos hl M.radius_bounds.1,(W.rescale_full hy).2⟩
    change sonicSpeed*M.localProfile (y/M.radius)=sonicSpeed ↔ _
    rw [mul_eq_left₀ (ne_of_gt sonicSpeed_bounds.1),hh,div_eq_one_iff_eq (ne_of_gt M.radius_bounds.1)]

lemma PhysicalWidth.sonic_slope {M : MatchedPair} (W : PhysicalWidth M) :
    0<deriv (fun y => velocityToU y (M.velocity y)) M.radius := by
  have he : (fun y => velocityToU y (M.velocity y)) =ᶠ[𝓝 M.radius] M.sonicU := by
    filter_upwards [Ioo_mem_nhds M.radius_bounds.1 W.endpoint_bounds.1] with y hy
    exact W.recover_U ⟨hy.1.le,hy.2.le⟩
  rw [he.deriv_eq,(M.sonicU_derivative (W.rescale_full ⟨M.radius_bounds.1.le,W.endpoint_bounds.1.le⟩)).deriv]
  rw [div_self (ne_of_gt M.radius_bounds.1)]
  exact mul_pos (div_pos (source_q_pos M.parameter) (by norm_num)) M.local_slope

end SepticProfile.SonicShooting

end
end

end OAI
