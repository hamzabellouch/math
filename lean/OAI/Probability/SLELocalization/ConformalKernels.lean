import Mathlib
import OAI.Probability.SLELocalization.CommonClocks

namespace OAI


/-! Conformal localization and Layer estimates. -/

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology RealInnerProductSpace
namespace SLEExactGauge.Layer

lemma logFactor_laplacian {z : ℂ} (hz : ‖z‖ < 1) :
    Laplacian.laplacian (fun z => Real.log (diskFactor z)) z = -4/(diskFactor z)^2 := by
  have ha := diskFactor_pos hz
  have hl : ContDiffAt ℝ 2 Real.log (diskFactor z) := Real.contDiffAt_log.mpr (ne_of_gt ha)
  have hh := laplacian_scalar_comp diskFactor_smooth.contDiffAt hl
  have hlogd : deriv Real.log = fun t => t⁻¹ := funext Real.deriv_log
  rw [diskFactor_laplacian,(diskFactor_gradient z).1,(diskFactor_gradient z).2,
    hlogd] at hh
  have he : deriv (fun t : ℝ => t⁻¹) (diskFactor z) = -((diskFactor z)^2)⁻¹ := by
    simp
  rw [he] at hh
  change Laplacian.laplacian (fun z => Real.log (diskFactor z)) z = _ at hh
  rw [hh]
  have hn : ‖z‖^2 = z.re^2+z.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
  dsimp [diskFactor] at ha ⊢
  rw [hn] at ha ⊢
  field_simp [ne_of_gt ha]
  ring

end SLEExactGauge.Layer

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology RealInnerProductSpace
namespace SLEExactGauge.Layer

lemma logNorm_fderiv {H : ℂ → ℂ} {z D : ℂ} (hd : HasDerivAt H D z)
    (hn : H z ≠ 0) (v : ℂ) :
    fderiv ℝ (fun w => Real.log ‖H w‖) z v = (D*v/H z).re := by
  have hn2 : ‖H z‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hn)
  have hh := ((hd.hasFDerivAt.restrictScalars ℝ).norm_sq.log hn2).const_smul (1/2:ℝ)
  have he : (fun w => (1/2:ℝ) • Real.log (‖H w‖^2)) = (fun w => Real.log ‖H w‖) := by
    funext w
    rw [Real.log_pow]
    simp only [smul_eq_mul]
    ring
  change HasFDerivAt (fun w => (1/2:ℝ) • Real.log (‖H w‖^2)) _ z at hh
  rw [he] at hh
  rw [hh.fderiv]
  simp only [smul_apply,smul_eq_mul,two_smul]
  change 1/2*((‖H z‖^2)⁻¹*(inner ℝ (H z) (v*D)+inner ℝ (H z) (v*D))) = (D*v/H z).re
  rw [Complex.inner,Complex.div_re]
  have heq : Complex.normSq (H z) = ‖H z‖^2 := (Complex.sq_norm _).symm
  rw [heq]
  simp only [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  field_simp
  ring

end SLEExactGauge.Layer

end

end

section
noncomputable section
open Set Filter Metric Function
open scoped Topology
namespace SLEExactGauge.Layer

structure DiskPair (U : Set ℂ) (F G : ℂ → ℂ) : Prop where
  isOpen : IsOpen U
  toDomain : MapsTo F (ball 0 1) U
  toDisk : MapsTo G U (ball 0 1)
  left_inv : ∀ z ∈ ball (0:ℂ) 1, G (F z) = z
  right_inv : ∀ z ∈ U, F (G z) = z
  forward : DifferentiableOn ℂ F (ball 0 1)
  inverse : DifferentiableOn ℂ G U

lemma DiskPair.injOn {U : Set ℂ} {F G : ℂ → ℂ} (h : DiskPair U F G) :
    InjOn F (ball 0 1) := by
  intro z hz w hw he
  simpa only [h.left_inv z hz,h.left_inv w hw] using congrArg G he

lemma DiskPair.inverse_derivative {U : Set ℂ} {F G : ℂ → ℂ} (h : DiskPair U F G)
    {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) : deriv G (F z)*deriv F z = 1 := by
  have he : (G ∘ F) =ᶠ[𝓝 z] id := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact h.left_inv w hw
  exact (((h.inverse.differentiableAt (h.isOpen.mem_nhds (h.toDomain hz))).hasDerivAt.comp z
    (h.forward.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt).congr_of_eventuallyEq he.symm).unique
      (hasDerivAt_id z)

lemma DiskPair.deriv_ne_zero {U : Set ℂ} {F G : ℂ → ℂ} (h : DiskPair U F G)
    {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) : deriv F z ≠ 0 := by
  intro he
  simpa [he] using h.inverse_derivative hz

lemma DiskPair.second_derivative_zero {U : Set ℂ} {F G : ℂ → ℂ} (h : DiskPair U F G) :
    ‖deriv (deriv F) 0‖ ≤ (2*(512*Real.pi)^2)*‖deriv F 0‖ := by
  have hzero : (0:ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hA : 0 < ‖deriv F 0‖ := norm_pos_iff.2 (h.deriv_ne_zero hzero)
  let R : ℝ := ‖deriv F 0‖/(512*Real.pi)
  have hR : 0 < R := div_pos hA (by positivity)
  have hsub : closedBall (F 0) R ⊆ U := by
    intro w hw
    by_contra hwu
    have hwi : w ∉ F '' ball 0 1 := by
      rintro ⟨z,hz,rfl⟩
      exact hwu (h.toDomain hz)
    have hh := UnivalentDistance.omitted_value_bound h.forward h.injOn hwi
    have hnorm : ‖F 0-w‖ ≤ R := by
      rw [norm_sub_rev,← dist_eq_norm]
      exact mem_closedBall.1 hw
    have hbound := hh.trans (mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ 256*Real.pi))
    have he : (256*Real.pi)*R = ‖deriv F 0‖/2 := by
      dsimp [R]; field_simp; ring
    rw [he] at hbound
    linarith
  have hb : ‖deriv (deriv G) (F 0)‖ ≤ 2/R^2 := by
    have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hR
      ((h.inverse.mono hsub).diffContOnCl_ball Subset.rfl)
      (fun z hz => (mem_ball_zero_iff.1 (h.toDisk (hsub (sphere_subset_closedBall hz)))).le)
    simpa [iteratedDeriv_succ,iteratedDeriv_zero] using hh
  have hFd := h.forward.differentiableAt (isOpen_ball.mem_nhds hzero)
  have hFdd := (h.forward.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hzero)
  have hGdd := (h.inverse.deriv h.isOpen).differentiableAt (h.isOpen.mem_nhds (h.toDomain hzero))
  have he : (fun z => deriv G (F z)*deriv F z) =ᶠ[𝓝 (0:ℂ)] fun _ => 1 := by
    filter_upwards [isOpen_ball.mem_nhds hzero] with z hz
    exact h.inverse_derivative hz
  have hh := (((hGdd.hasDerivAt.comp 0 hFd.hasDerivAt).mul hFdd.hasDerivAt).congr_of_eventuallyEq
    he.symm).unique (hasDerivAt_const (0:ℂ) (1:ℂ))
  simp only [Function.comp_apply] at hh
  have hh0 := h.inverse_derivative hzero
  have hrel : deriv (deriv F) 0 = -deriv (deriv G) (F 0)*(deriv F 0)^3 := by
    linear_combination (deriv F 0)*hh - (deriv (deriv F) 0)*hh0
  rw [hrel,norm_mul,norm_neg,norm_pow]
  calc
    _ ≤ (2/R^2)*‖deriv F 0‖^3 := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (2*(512*Real.pi)^2)*‖deriv F 0‖ := by
      dsimp [R]
      field_simp

end SLEExactGauge.Layer

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology
namespace SLEExactGauge.SlitMaps

def diskAuto (c z : ℂ) : ℂ := (z-c)/(1-starRingEnd ℂ c*z)

lemma diskAuto_den_ne {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ < 1) :
    1-starRingEnd ℂ c*z ≠ 0 := by
  have hn : ‖starRingEnd ℂ c*z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc
      ‖c‖*‖z‖ ≤ ‖c‖*1 := mul_le_mul_of_nonneg_left hz.le (norm_nonneg _)
      _ < 1 := by simpa using hc
  intro he
  have hh : starRingEnd ℂ c*z = 1 := (sub_eq_zero.1 he).symm
  simp [hh] at hn

lemma disk_norm_identity (c z : ℂ) :
    ‖1-starRingEnd ℂ c*z‖^2-‖z-c‖^2 = (1-‖c‖^2)*(1-‖z‖^2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

lemma diskAuto_mapsTo {c : ℂ} (hc : ‖c‖ < 1) : MapsTo (diskAuto c) (ball 0 1) (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz ⊢
  have hn := diskAuto_den_ne hc hz
  rw [diskAuto,norm_div,div_lt_one₀ (norm_pos_iff.2 hn)]
  have hp : 0 < (1-‖c‖^2)*(1-‖z‖^2) := mul_pos (by nlinarith [norm_nonneg c]) (by nlinarith [norm_nonneg z])
  have he := disk_norm_identity c z
  nlinarith [norm_nonneg (z-c), norm_nonneg (1-starRingEnd ℂ c*z)]

lemma diskAuto_hasDerivAt {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (diskAuto c) ((1-starRingEnd ℂ c*c)/(1-starRingEnd ℂ c*z)^2) z := by
  have hd := ((hasDerivAt_id z).sub_const c).div
    ((hasDerivAt_const z (1:ℂ)).sub ((hasDerivAt_id z).const_mul (starRingEnd ℂ c)))
    (diskAuto_den_ne hc hz)
  change HasDerivAt (diskAuto c)
    ((1*(1-starRingEnd ℂ c*z)-(z-c)*(0-starRingEnd ℂ c*1))/(1-starRingEnd ℂ c*z)^2) z at hd
  have he : 1*(1-starRingEnd ℂ c*z)-(z-c)*(0-starRingEnd ℂ c*1) = 1-starRingEnd ℂ c*c := by ring
  rwa [he] at hd

lemma diskAuto_deriv {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ < 1) :
    deriv (diskAuto c) z = (1-starRingEnd ℂ c*c)/(1-starRingEnd ℂ c*z)^2 :=
  (diskAuto_hasDerivAt hc hz).deriv

lemma diskAuto_deriv_ne {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ < 1) :
    deriv (diskAuto c) z ≠ 0 := by
  rw [diskAuto_deriv hc hz]
  exact div_ne_zero (diskAuto_den_ne hc hc) (pow_ne_zero _ (diskAuto_den_ne hc hz))

lemma diskAuto_injOn {c : ℂ} (hc : ‖c‖ < 1) : InjOn (diskAuto c) (ball 0 1) := by
  intro z hz w hw he
  have hzn := diskAuto_den_ne hc (mem_ball_zero_iff.1 hz)
  have hwn := diskAuto_den_ne hc (mem_ball_zero_iff.1 hw)
  have he' := (div_eq_div_iff hzn hwn).1 he
  have hn := diskAuto_den_ne hc hc
  have hh : (z-w)*(1-starRingEnd ℂ c*c) = 0 := by linear_combination he'
  exact sub_eq_zero.1 ((mul_eq_zero.1 hh).resolve_right hn)

@[simp] lemma diskAuto_self (c : ℂ) : diskAuto c c = 0 := by simp [diskAuto]

@[simp] lemma diskAuto_zero (c : ℂ) : diskAuto c 0 = -c := by simp [diskAuto]

lemma diskAuto_norm_deriv_zero {c : ℂ} (hc : ‖c‖ < 1) :
    ‖deriv (diskAuto c) 0‖ = 1-‖c‖^2 := by
  rw [diskAuto_deriv hc (by simp)]
  simp only [mul_zero,sub_zero,one_pow,div_one]
  rw [mul_comm (starRingEnd ℂ c),Complex.mul_conj']
  have he : (1:ℂ)-(‖c‖:ℂ)^2 = ((1-‖c‖^2:ℝ):ℂ) := by push_cast; rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by nlinarith [norm_nonneg c])]

lemma diskAuto_norm_deriv_self {c : ℂ} (hc : ‖c‖ < 1) :
    ‖deriv (diskAuto c) c‖ = 1/(1-‖c‖^2) := by
  have hh : (1-starRingEnd ℂ c*c)/(1-starRingEnd ℂ c*c)^2 = (1-starRingEnd ℂ c*c)⁻¹ := by
    field_simp [diskAuto_den_ne hc hc]
  rw [diskAuto_deriv hc hc,hh]
  rw [norm_inv]
  have he : ‖1-starRingEnd ℂ c*c‖ = 1-‖c‖^2 := by
    have hh := diskAuto_norm_deriv_zero hc
    rw [diskAuto_deriv hc (by simp)] at hh
    simpa using hh
  simp [he,one_div]

end SLEExactGauge.SlitMaps

end

end

section
noncomputable section
open Set Filter Metric Function
open scoped Topology
namespace SLEExactGauge.Layer
open SlitMaps

lemma diskAuto_neg_inverse {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ < 1) :
    diskAuto c (diskAuto (-c) z) = z := by
  have hnc : ‖-c‖ < 1 := by simpa using hc
  have hφ := diskAuto_mapsTo hnc (mem_ball_zero_iff.2 hz)
  have hd1 := diskAuto_den_ne hnc hz
  have hd2 := diskAuto_den_ne hc (mem_ball_zero_iff.1 hφ)
  have ha := diskAuto_den_ne hc hc
  dsimp [diskAuto] at hd1 hd2 ⊢
  simp only [map_neg,neg_mul,sub_neg_eq_add] at hd1 hd2 ⊢
  apply (div_eq_iff hd2).2
  have he := div_mul_cancel₀ (z+c) hd1
  linear_combination he

lemma DiskPair.recenter {U : Set ℂ} {F G : ℂ → ℂ} (h : DiskPair U F G)
    {c : ℂ} (hc : ‖c‖ < 1) :
    DiskPair U (F ∘ diskAuto (-c)) (diskAuto c ∘ G) := by
  have hnc : ‖-c‖ < 1 := by simpa using hc
  refine ⟨h.isOpen,h.toDomain.comp (diskAuto_mapsTo hnc),(diskAuto_mapsTo hc).comp h.toDisk,?_,?_,?_,?_⟩
  · intro z hz
    dsimp only [Function.comp_apply]
    rw [h.left_inv _ (diskAuto_mapsTo hnc hz)]
    exact diskAuto_neg_inverse hc (mem_ball_zero_iff.1 hz)
  · intro z hz
    dsimp only [Function.comp_apply]
    have he := diskAuto_neg_inverse hnc (mem_ball_zero_iff.1 (h.toDisk hz))
    simp only [neg_neg] at he
    rw [he,h.right_inv z hz]
  · exact h.forward.comp (fun z hz => (diskAuto_hasDerivAt hnc (mem_ball_zero_iff.1 hz)).differentiableAt.differentiableWithinAt)
      (diskAuto_mapsTo hnc)
  · have ha : DifferentiableOn ℂ (diskAuto c) (ball 0 1) := fun z hz =>
      (diskAuto_hasDerivAt hc (mem_ball_zero_iff.1 hz)).differentiableAt.differentiableWithinAt
    exact ha.comp h.inverse h.toDisk

lemma diskAuto_deriv_zero_exact {c : ℂ} (hc : ‖c‖ < 1) :
    deriv (diskAuto (-c)) 0 = 1-(starRingEnd ℂ c)*c := by
  rw [diskAuto_deriv (by simpa using hc) (by simp)]
  simp

lemma diskAuto_second_zero {c : ℂ} (hc : ‖c‖ < 1) :
    deriv (deriv (diskAuto (-c))) 0 = -2*(starRingEnd ℂ c)*(1-(starRingEnd ℂ c)*c) := by
  have hnc : ‖-c‖ < 1 := by simpa using hc
  have he : deriv (diskAuto (-c)) =ᶠ[𝓝 (0:ℂ)]
      fun z => (1-(starRingEnd ℂ c)*c)/(1+(starRingEnd ℂ c)*z)^2 := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) zero_lt_one] with z hz
    rw [diskAuto_deriv hnc (mem_ball_zero_iff.1 hz)]
    simp
  rw [he.deriv_eq]
  have hd := (hasDerivAt_const (0:ℂ) (1-(starRingEnd ℂ c)*c)).div
    ((((hasDerivAt_id (0:ℂ)).const_mul (starRingEnd ℂ c)).const_add 1).pow 2) (by simp)
  have hh := hd.deriv
  dsimp only [Pi.div_apply,Pi.pow_apply,id_eq] at hh
  change deriv ((fun x : ℂ => 1-(starRingEnd ℂ c)*c) / (fun x : ℂ => 1+(starRingEnd ℂ c)*x)^2) 0 = _
  rw [hh]
  simp only [mul_zero,add_zero,one_pow,zero_sub,div_one,mul_one]
  norm_num
  ring

lemma DiskPair.preSchwarzian {U : Set ℂ} {F G : ℂ → ℂ} (h : DiskPair U F G)
    {c : ℂ} (hc : ‖c‖ < 1) :
    ‖((1-‖c‖^2:ℝ):ℂ)*deriv (deriv F) c - 2*(starRingEnd ℂ c)*deriv F c‖ ≤
      (2*(512*Real.pi)^2)*‖deriv F c‖ := by
  let φ := diskAuto (-c)
  let A : ℂ := 1-(starRingEnd ℂ c)*c
  have hnc : ‖-c‖ < 1 := by simpa using hc
  have hcD : c ∈ ball (0:ℂ) 1 := mem_ball_zero_iff.2 hc
  have hφ0 : φ 0 = c := by simp [φ]
  have hdφ : deriv φ 0 = A := diskAuto_deriv_zero_exact hc
  have hddφ : deriv (deriv φ) 0 = -2*(starRingEnd ℂ c)*A := diskAuto_second_zero hc
  have hφd : DifferentiableOn ℂ φ (ball 0 1) := fun z hz =>
    (diskAuto_hasDerivAt hnc (mem_ball_zero_iff.1 hz)).differentiableAt.differentiableWithinAt
  have hFd := h.forward.differentiableAt (isOpen_ball.mem_nhds hcD)
  have hFdd := (h.forward.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hcD)
  have hφd0 := hφd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))
  have hφdd0 := (hφd.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))
  have hd : deriv (F ∘ φ) 0 = deriv F c*A := by
    have hFd' : HasDerivAt F (deriv F c) (φ 0) := hφ0.symm ▸ hFd.hasDerivAt
    have hh := hFd'.comp (0:ℂ) hφd0.hasDerivAt
    simpa only [hdφ] using hh.deriv
  have he : deriv (F ∘ φ) =ᶠ[𝓝 (0:ℂ)] fun z => deriv F (φ z)*deriv φ z := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) zero_lt_one] with z hz
    exact ((h.forward.differentiableAt (isOpen_ball.mem_nhds (diskAuto_mapsTo hnc hz))).hasDerivAt.comp z
      (hφd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt).deriv
  have hdd : deriv (deriv (F ∘ φ)) 0 = A*(A*deriv (deriv F) c-2*(starRingEnd ℂ c)*deriv F c) := by
    rw [he.deriv_eq]
    have hFdd' : HasDerivAt (deriv F) (deriv (deriv F) c) (φ 0) := hφ0.symm ▸ hFdd.hasDerivAt
    have hh := ((hFdd'.comp 0 hφd0.hasDerivAt).mul hφdd0.hasDerivAt).deriv
    dsimp only [Pi.mul_apply,Function.comp_apply] at hh
    simp only [hφ0,hdφ,hddφ] at hh
    change deriv ((deriv F ∘ φ)*deriv φ) 0 = _
    rw [hh]
    ring
  have hAeq : A = ((1-‖c‖^2:ℝ):ℂ) := by
    dsimp only [A]
    rw [mul_comm (starRingEnd ℂ c),Complex.mul_conj']
    push_cast
    rfl
  have hAp : 0 < ‖A‖ := by
    rw [hAeq,Complex.norm_real,Real.norm_eq_abs]
    exact abs_pos.2 (by nlinarith [norm_nonneg c] : 1-‖c‖^2 ≠ 0)
  have hb := (h.recenter hc).second_derivative_zero
  change ‖deriv (deriv (F ∘ φ)) 0‖ ≤ (2*(512*Real.pi)^2)*‖deriv (F ∘ φ) 0‖ at hb
  rw [hdd,hd,norm_mul,norm_mul] at hb
  have hh : ‖A*deriv (deriv F) c-2*(starRingEnd ℂ c)*deriv F c‖ ≤ (2*(512*Real.pi)^2)*‖deriv F c‖ := by
    nlinarith
  rwa [hAeq] at hh

end SLEExactGauge.Layer

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology
namespace SLEExactGauge.Layer

def logRadius (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  Real.log (diskFactor z) + Real.log ‖deriv F z‖

lemma DiskPair.logRadius_smooth {U : Set ℂ} {F G : ℂ → ℂ}
    (h : DiskPair U F G) {z : ℂ} (hz : ‖z‖ < 1) :
    ContDiffAt ℝ 2 (logRadius F) z := by
  have hh := ((h.forward.deriv isOpen_ball).analyticOnNhd isOpen_ball z
    (mem_ball_zero_iff.2 hz)).harmonicAt_log_norm (h.deriv_ne_zero (mem_ball_zero_iff.2 hz))
  exact (logFactor_smooth hz).add hh.1

lemma DiskPair.logRadius_laplacian {U : Set ℂ} {F G : ℂ → ℂ}
    (h : DiskPair U F G) {z : ℂ} (hz : ‖z‖ < 1) :
    Laplacian.laplacian (logRadius F) z = -4/(diskFactor z)^2 := by
  have hh := ((h.forward.deriv isOpen_ball).analyticOnNhd isOpen_ball z
    (mem_ball_zero_iff.2 hz)).harmonicAt_log_norm (h.deriv_ne_zero (mem_ball_zero_iff.2 hz))
  have he := (logFactor_smooth hz).laplacian_add hh.1
  change Laplacian.laplacian (logRadius F) z = _ at he
  rw [he,logFactor_laplacian hz,hh.2.eq_of_nhds]
  simp

lemma DiskPair.logRadius_gradient {U : Set ℂ} {F G : ℂ → ℂ}
    (h : DiskPair U F G) {z : ℂ} (hz : ‖z‖ < 1) :
    fderiv ℝ (logRadius F) z 1 = (deriv (deriv F) z/deriv F z).re - 2*z.re/diskFactor z ∧
    fderiv ℝ (logRadius F) z Complex.I = -(deriv (deriv F) z/deriv F z).im - 2*z.im/diskFactor z := by
  have ha := diskFactor_pos hz
  have hdz := (h.forward.deriv isOpen_ball).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz))
  have hn := h.deriv_ne_zero (mem_ball_zero_iff.2 hz)
  have hl := (diskFactor_smooth.differentiable (by norm_num) z).hasFDerivAt.log (ne_of_gt ha)
  have hd : DifferentiableAt ℝ (fun z => Real.log ‖deriv F z‖) z :=
    (((h.forward.deriv isOpen_ball).analyticOnNhd isOpen_ball z
      (mem_ball_zero_iff.2 hz)).harmonicAt_log_norm hn).1.differentiableAt (by norm_num)
  have he := (hl.add hd.hasFDerivAt).fderiv
  change fderiv ℝ (logRadius F) z = _ at he
  rw [he]
  simp only [add_apply,smul_apply,smul_eq_mul,
    (diskFactor_gradient z).1,(diskFactor_gradient z).2,
    logNorm_fderiv hdz.hasDerivAt hn,mul_one]
  constructor
  · ring
  · rw [mul_div_right_comm,Complex.mul_re]
    simp
    ring

lemma DiskPair.logRadius_gradient_sq {U : Set ℂ} {F G : ℂ → ℂ}
    (h : DiskPair U F G) {z : ℂ} (hz : ‖z‖ < 1) :
    (fderiv ℝ (logRadius F) z 1)^2 + (fderiv ℝ (logRadius F) z Complex.I)^2 ≤
      (2*(512*Real.pi)^2)^2/(diskFactor z)^2 := by
  let a := diskFactor z
  let c := deriv (deriv F) z/deriv F z
  let b : ℂ := (a:ℂ)*c - 2*(starRingEnd ℂ z)
  have ha : 0 < a := diskFactor_pos hz
  have hn := h.deriv_ne_zero (mem_ball_zero_iff.2 hz)
  have he : b = ((a:ℂ)*deriv (deriv F) z - 2*(starRingEnd ℂ z)*deriv F z)/deriv F z := by
    dsimp [b,c]
    field_simp
  have hb : ‖b‖ ≤ 2*(512*Real.pi)^2 := by
    rw [he,norm_div]
    apply (div_le_iff₀ (norm_pos_iff.2 hn)).2
    exact h.preSchwarzian hz
  have hi : ((fderiv ℝ (logRadius F) z 1)^2 +
      (fderiv ℝ (logRadius F) z Complex.I)^2)*a^2 = ‖b‖^2 := by
    rw [(h.logRadius_gradient hz).1,(h.logRadius_gradient hz).2,
      Complex.sq_norm,Complex.normSq_apply]
    change ((c.re-2*z.re/a)^2+(-c.im-2*z.im/a)^2)*a^2 = _
    dsimp [b]
    simp only [Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,
      Complex.conj_re,Complex.conj_im,zero_mul,sub_zero,add_zero]
    norm_num
    field_simp
    ring
  apply (le_div_iff₀ (pow_pos ha 2)).2
  rw [hi]
  exact pow_le_pow_left₀ (norm_nonneg b) hb 2

end SLEExactGauge.Layer

end

end

section
noncomputable section
open Set Filter
open scoped Topology
namespace SLEExactGauge.Layer

def layerProfile (α t : ℝ) : ℝ := Real.exp (α*t)/(1+Real.exp (α*t))

def layerProfileD (α t : ℝ) : ℝ := α*Real.exp (α*t)/(1+Real.exp (α*t))^2

def layerProfileDD (α t : ℝ) : ℝ :=
  α^2*Real.exp (α*t)*(1-Real.exp (α*t))/(1+Real.exp (α*t))^3

lemma profile_smooth (α : ℝ) : ContDiff ℝ 2 (layerProfile α) := by
  unfold layerProfile
  apply ContDiff.div (by fun_prop) (by fun_prop)
  intro x
  positivity

lemma profile_derivative (α t : ℝ) : HasDerivAt (layerProfile α) (layerProfileD α t) t := by
  have he := ((hasDerivAt_id t).const_mul α).exp
  have hh := he.div (he.const_add 1) (by positivity : 1+Real.exp (α*t) ≠ 0)
  convert! hh using 1
  dsimp [layerProfile,layerProfileD]
  ring

lemma profile_second (α t : ℝ) : HasDerivAt (layerProfileD α) (layerProfileDD α t) t := by
  have he := ((hasDerivAt_id t).const_mul α).exp
  have hh := (he.const_mul α).div ((he.const_add 1).pow 2)
    (by positivity : (1+Real.exp (α*t))^2 ≠ 0)
  convert! hh using 1
  dsimp [layerProfileD,layerProfileDD]
  field_simp
  ring

lemma profile_bounds (α t : ℝ) : 0 ≤ layerProfile α t ∧ layerProfile α t ≤ 1 := by
  have he := Real.exp_pos (α*t)
  dsimp [layerProfile]
  exact ⟨by positivity,(div_le_one (by positivity)).2 (by linarith)⟩

lemma profileD_nonneg {α : ℝ} (hα : 0 ≤ α) (t : ℝ) : 0 ≤ layerProfileD α t := by
  dsimp [layerProfileD]
  positivity

lemma profileDD_le {α : ℝ} (_hα : 0 ≤ α) (t : ℝ) :
    layerProfileDD α t ≤ α*layerProfileD α t := by
  have he := Real.exp_pos (α*t)
  have hd : 0 < 1+Real.exp (α*t) := by positivity
  rw [layerProfileDD,layerProfileD,div_le_iff₀ (pow_pos hd 3)]
  have hi : α*(α*Real.exp (α*t)/(1+Real.exp (α*t))^2)*(1+Real.exp (α*t))^3 =
      α^2*Real.exp (α*t)*(1+Real.exp (α*t)) := by field_simp
  rw [hi]
  exact mul_le_mul_of_nonneg_left (by linarith : 1-Real.exp (α*t) ≤ 1+Real.exp (α*t)) (by positivity)

lemma profileD_lower {α t : ℝ} (hα : 0 ≤ α) (hα₂ : α ≤ 2) (ht : t ≤ 0) :
    α*Real.exp (2*t)/4 ≤ layerProfileD α t := by
  have he := Real.exp_pos (α*t)
  have he1 : Real.exp (α*t) ≤ 1 := Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos hα ht)
  have he2 : Real.exp (2*t) ≤ Real.exp (α*t) := Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right hα₂ ht)
  have hden : (1+Real.exp (α*t))^2 ≤ 4 := by nlinarith
  calc
    _ ≤ α*Real.exp (α*t)/4 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he2 hα) (by norm_num)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hden

end SLEExactGauge.Layer

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology
namespace SLEExactGauge.Layer

def layerExponent : ℝ := 1/(1+(2*(512*Real.pi)^2)^2)

lemma layerExponent_bounds : 0 < layerExponent ∧ layerExponent ≤ 2 ∧
    layerExponent*(2*(512*Real.pi)^2)^2 ≤ 2 := by
  have hL : 0 ≤ (2*(512*Real.pi)^2)^2 := sq_nonneg _
  have hd : 0 < 1+(2*(512*Real.pi)^2)^2 := by positivity
  dsimp [layerExponent]
  refine ⟨by positivity,?_,?_⟩
  · apply (div_le_iff₀ hd).2
    nlinarith
  · rw [div_mul_eq_mul_div,mul_comm (1:ℝ),mul_one]
    apply (div_le_iff₀ hd).2
    linarith

def shiftedRadius (F : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℝ := logRadius F z - Real.log R

def layerBarrier (F : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℝ :=
  R^2 * layerProfile layerExponent (shiftedRadius F R z)

lemma DiskPair.shifted_smooth {U : Set ℂ} {F G : ℂ → ℂ}
    (h : DiskPair U F G) {z : ℂ} (hz : ‖z‖ < 1) (R : ℝ) :
    ContDiffAt ℝ 2 (shiftedRadius F R) z := (h.logRadius_smooth hz).sub contDiffAt_const

lemma DiskPair.shifted_laplacian {U : Set ℂ} {F G : ℂ → ℂ}
    (h : DiskPair U F G) {z : ℂ} (hz : ‖z‖ < 1) (R : ℝ) :
    Laplacian.laplacian (shiftedRadius F R) z = -4/(diskFactor z)^2 := by
  have hh := (h.logRadius_smooth hz).laplacian_sub (contDiffAt_const (c := Real.log R))
  change Laplacian.laplacian (shiftedRadius F R) z = _ at hh
  rw [hh,h.logRadius_laplacian hz]
  simp

lemma shifted_fderiv (F : ℂ → ℂ) (R : ℝ) (z : ℂ) :
    fderiv ℝ (shiftedRadius F R) z = fderiv ℝ (logRadius F) z := fderiv_sub_const _

lemma DiskPair.barrier_smooth {U : Set ℂ} {F G : ℂ → ℂ}
    (h : DiskPair U F G) (R : ℝ) : ContDiffOn ℝ 2 (layerBarrier F R) (ball 0 1) := by
  intro z hz
  exact (((profile_smooth layerExponent).contDiffAt.comp z
    (h.shifted_smooth (mem_ball_zero_iff.1 hz) R)).const_smul (R^2)).contDiffWithinAt

lemma barrier_bounds (F : ℂ → ℂ) (R : ℝ) (z : ℂ) :
    0 ≤ layerBarrier F R z ∧ layerBarrier F R z ≤ R^2 := by
  have hh := profile_bounds layerExponent (shiftedRadius F R z)
  dsimp [layerBarrier]
  exact ⟨mul_nonneg (sq_nonneg _) hh.1,by simpa using mul_le_mul_of_nonneg_left hh.2 (sq_nonneg R)⟩

lemma profile_laplacian_estimate {u : ℂ → ℝ} {z : ℂ} {a α L : ℝ}
    (hu : ContDiffAt ℝ 2 u z) (_ha : 0 < a) (hα : 0 ≤ α) (hαL : α*L ≤ 2)
    (hΔ : Laplacian.laplacian u z = -4/a^2)
    (hgrad : (fderiv ℝ u z 1)^2+(fderiv ℝ u z Complex.I)^2 ≤ L/a^2) :
    Laplacian.laplacian (layerProfile α ∘ u) z ≤ -2*layerProfileD α (u z)/a^2 := by
  rw [laplacian_scalar_comp hu (profile_smooth α).contDiffAt]
  have hd : deriv (layerProfile α) = layerProfileD α := funext (fun t => (profile_derivative α t).deriv)
  rw [hd,(profile_second α (u z)).deriv,hΔ]
  have hD := profileD_nonneg hα (u z)
  have hDD := profileDD_le hα (u z)
  calc
    _ ≤ (α*layerProfileD α (u z))*(L/a^2) + layerProfileD α (u z)*(-4/a^2) := by
      apply add_le_add_left
      exact (mul_le_mul_of_nonneg_right hDD (add_nonneg (sq_nonneg _) (sq_nonneg _))).trans
        (mul_le_mul_of_nonneg_left hgrad (mul_nonneg hα hD))
    _ = layerProfileD α (u z)*(α*L-4)/a^2 := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg a)
      nlinarith [mul_le_mul_of_nonneg_left hαL hD]

lemma DiskPair.barrier_drop {U : Set ℂ} {F G : ℂ → ℂ}
    (h : DiskPair U F G) {z : ℂ} (hz : ‖z‖ < 1) (R : ℝ) :
    Laplacian.laplacian (layerBarrier F R) z ≤
      -2*R^2*layerProfileD layerExponent (shiftedRadius F R z)/(diskFactor z)^2 := by
  have hs := h.shifted_smooth hz R
  have hc := (profile_smooth layerExponent).contDiffAt.comp z hs
  have hh := InnerProductSpace.laplacian_smul (R^2) hc
  change Laplacian.laplacian (layerBarrier F R) z = R^2*Laplacian.laplacian (layerProfile layerExponent ∘ shiftedRadius F R) z at hh
  rw [hh]
  have hb := profile_laplacian_estimate hs (diskFactor_pos hz)
    layerExponent_bounds.1.le layerExponent_bounds.2.2 (h.shifted_laplacian hz R)
    (by rw [shifted_fderiv]; exact h.logRadius_gradient_sq hz)
  convert! mul_le_mul_of_nonneg_left hb (sq_nonneg R) using 1
  ring

lemma DiskPair.barrier_superharmonic {U : Set ℂ} {F G : ℂ → ℂ}
    (h : DiskPair U F G) {z : ℂ} (hz : ‖z‖ < 1) (R : ℝ) :
    Laplacian.laplacian (layerBarrier F R) z ≤ 0 := by
  apply (h.barrier_drop hz R).trans
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have hh := profileD_nonneg layerExponent_bounds.1.le (shiftedRadius F R z)
  nlinarith [sq_nonneg R]

lemma DiskPair.shifted_exp {U : Set ℂ} {F G : ℂ → ℂ}
    (h : DiskPair U F G) {z : ℂ} (hz : ‖z‖ < 1) {R : ℝ} (hR : 0 < R) :
    Real.exp (shiftedRadius F R z) = diskFactor z * ‖deriv F z‖/R := by
  have ha := diskFactor_pos hz
  have hn := norm_pos_iff.2 (h.deriv_ne_zero (mem_ball_zero_iff.2 hz))
  dsimp [shiftedRadius,logRadius]
  rw [Real.exp_sub,Real.exp_add,Real.exp_log ha,Real.exp_log hn,Real.exp_log hR]

lemma DiskPair.barrier_layer {U : Set ℂ} {F G : ℂ → ℂ}
    (h : DiskPair U F G) {z : ℂ} (hz : ‖z‖ < 1) {R : ℝ} (hR : 0 < R)
    (hl : diskFactor z * ‖deriv F z‖ ≤ R) :
    layerExponent/2*‖deriv F z‖^2 ≤ -Laplacian.laplacian (layerBarrier F R) z := by
  have ha := diskFactor_pos hz
  have ht : shiftedRadius F R z ≤ 0 := by
    apply Real.exp_le_one_iff.1
    rw [h.shifted_exp hz hR]
    exact (div_le_one hR).2 hl
  have he : Real.exp (2*shiftedRadius F R z) = (diskFactor z * ‖deriv F z‖/R)^2 := by
    rw [two_mul,Real.exp_add,h.shifted_exp hz hR,pow_two]
  have hp := profileD_lower layerExponent_bounds.1.le layerExponent_bounds.2.1 ht
  rw [he] at hp
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2*R^2/(diskFactor z)^2 by positivity)
  have hid : (2*R^2/(diskFactor z)^2)*(layerExponent*(diskFactor z*‖deriv F z‖/R)^2/4) =
      layerExponent/2*‖deriv F z‖^2 := by
    field_simp
    ring
  rw [hid] at hm
  have hb := h.barrier_drop hz R
  nlinarith [show (2*R^2/(diskFactor z)^2)*layerProfileD layerExponent (shiftedRadius F R z) =
      -(-2*R^2*layerProfileD layerExponent (shiftedRadius F R z)/(diskFactor z)^2) by ring]

end SLEExactGauge.Layer

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace SLEExactGauge.Layer

lemma radial_green_annulus {m d L : ℝ → ℝ} {M e R : ℝ}
    (he : 0 < e) (heR : e ≤ R) (hR : R < 1)
    (hd : ∀ r ∈ Ico (0:ℝ) 1, HasDerivAt m (d r) r)
    (hc : ContinuousOn d (Ico (0:ℝ) 1))
    (hA : ∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt (fun r => r*d r) (r*L r) r)
    (hLc : ContinuousOn L (Ioo (0:ℝ) 1))
    (hL : ∀ r ∈ Ioo (0:ℝ) 1, L r ≤ 0)
    (hm : ∀ r ∈ Ico (0:ℝ) 1, 0 ≤ m r ∧ m r ≤ M) :
    (∫ r in e..R, Real.log (R/r)*(-r*L r)) ≤ M := by
  have hR0 : 0 < R := he.trans_le heR
  have hsub : Icc (0:ℝ) R ⊆ Ico (0:ℝ) 1 := fun r hr => ⟨hr.1,hr.2.trans_lt hR⟩
  have hant : AntitoneOn (fun r => r*d r) (Icc (0:ℝ) R) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (continuousOn_id.mul (hc.mono hsub))
    · intro r hr
      rw [interior_Icc] at hr
      exact (hA r ⟨hr.1,hr.2.trans hR⟩).hasDerivWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      exact mul_nonpos_of_nonneg_of_nonpos hr.1.le (hL r ⟨hr.1,hr.2.trans hR⟩)
  have hAe : e*d e ≤ 0 := by
    simpa using hant ⟨le_rfl,hR0.le⟩ ⟨he.le,heR⟩ he.le
  have hue : uIcc e R = Icc e R := uIcc_of_le heR
  have hs (r : ℝ) (hr : r ∈ uIcc e R) : r ∈ Ioo (0:ℝ) 1 := by
    rw [hue] at hr
    exact ⟨he.trans_le hr.1,hr.2.trans_lt hR⟩
  have hlog (r : ℝ) (hr : r ∈ uIcc e R) :
      HasDerivAt (fun r => Real.log (R/r)) (-r⁻¹) r := by
    have hh := (Real.hasDerivAt_log (ne_of_gt (hs r hr).1)).const_sub (Real.log R)
    convert hh.congr_of_eventuallyEq ?_ using 1
    filter_upwards [Ioi_mem_nhds (hs r hr).1] with t ht
    exact Real.log_div (ne_of_gt hR0) (ne_of_gt ht)
  have hprim (r : ℝ) (hr : r ∈ uIcc e R) :
      HasDerivAt (fun r => -Real.log (R/r)*(r*d r)-m r)
        (Real.log (R/r)*(-r*L r)) r := by
    have hh := ((hlog r hr).neg.mul (hA r (hs r hr))).sub (hd r ⟨(hs r hr).1.le,(hs r hr).2⟩)
    convert! hh using 1
    simp only [Pi.neg_apply,neg_neg]
    field_simp [ne_of_gt (hs r hr).1]
    ring
  have hi : IntervalIntegrable (fun r => Real.log (R/r)*(-r*L r)) volume e R := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
    · exact fun r hr => (hlog r hr).continuousAt.continuousWithinAt
    · exact (continuousOn_id.neg.mul (hLc.mono (fun r hr => hs r hr)))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hprim hi
  have hRR : Real.log (R/R) = 0 := by simp [ne_of_gt hR0]
  rw [hRR,neg_zero,zero_mul,zero_sub] at hftc
  rw [hftc]
  have hlg : 0 ≤ Real.log (R/e) := Real.log_nonneg ((one_le_div he).2 heR)
  have hmul := mul_nonpos_of_nonneg_of_nonpos hlg hAe
  have hme := hm e ⟨he.le,heR.trans_lt hR⟩
  have hmR := hm R ⟨hR0.le,hR⟩
  nlinarith

end SLEExactGauge.Layer

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace SLEExactGauge.Layer

lemma radial_green_integral {m d L : ℝ → ℝ} {M : ℝ}
    (hd : ∀ r ∈ Ico (0:ℝ) 1, HasDerivAt m (d r) r)
    (hc : ContinuousOn d (Ico (0:ℝ) 1))
    (hA : ∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt (fun r => r*d r) (r*L r) r)
    (hLc : ContinuousOn L (Ioo (0:ℝ) 1))
    (hL : ∀ r ∈ Ioo (0:ℝ) 1, L r ≤ 0)
    (hm : ∀ r ∈ Ico (0:ℝ) 1, 0 ≤ m r ∧ m r ≤ M) :
    (∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal (Real.log (1/r)*(-r*L r))) ≤ ENNReal.ofReal M := by
  let e : ℕ → ℝ := fun n => (1/((n:ℝ)+1))/2
  let R : ℕ → ℝ := fun n => 1-e n
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have hehalf (n : ℕ) : e n ≤ 1/2 := by
    dsimp [e]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact (div_le_one (by positivity)).2 (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)
  have heR (n : ℕ) : e n ≤ R n := by dsimp [R]; linarith [hehalf n]
  have hR (n : ℕ) : R n < 1 := by dsimp [R]; linarith [he n]
  have hR0 (n : ℕ) : 0 < R n := (he n).trans_le (heR n)
  have hsub (n : ℕ) : Icc (e n) (R n) ⊆ Ioo (0:ℝ) 1 :=
    fun r hr => ⟨(he n).trans_le hr.1,hr.2.trans_lt (hR n)⟩
  let f : ℕ → ℝ → ℝ≥0∞ := fun n => (Icc (e n) (R n)).indicator
    (fun r => ENNReal.ofReal (Real.log (R n/r)*(-r*L r)))
  let μ := volume.restrict (Ioo (0:ℝ) 1)
  have hfm (n : ℕ) : AEMeasurable (f n) μ := by
    apply AEMeasurable.indicator _ measurableSet_Icc
    apply AEMeasurable.ennreal_ofReal
    exact ((measurable_const.div measurable_id).log.aemeasurable).mul
      (measurable_id.neg.aemeasurable.mul (hLc.aemeasurable measurableSet_Ioo))
  have hbound (n : ℕ) : (∫⁻ r, f n r ∂μ) ≤ ENNReal.ofReal M := by
    let q : ℝ → ℝ := fun r => Real.log (R n/r)*(-r*L r)
    have hqc : ContinuousOn q (Icc (e n) (R n)) := by
      apply ContinuousOn.mul
      · exact (continuousOn_const.div continuousOn_id (fun r hr => ne_of_gt (hsub n hr).1)).log
          (fun r hr => ne_of_gt (div_pos (hR0 n) (hsub n hr).1))
      · exact continuousOn_id.neg.mul (hLc.mono (hsub n))
    have hqi : IntegrableOn q (Icc (e n) (R n)) := hqc.integrableOn_Icc
    have hqnn : 0 ≤ᵐ[volume.restrict (Icc (e n) (R n))] q := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact mul_nonneg (Real.log_nonneg ((one_le_div (hsub n hr).1).2 hr.2))
        (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 (hsub n hr).1.le) (hL r (hsub n hr)))
    change (∫⁻ r, (Icc (e n) (R n)).indicator (fun r => ENNReal.ofReal (q r)) r ∂μ) ≤ _
    rw [lintegral_indicator measurableSet_Icc]
    change (∫⁻ r, ENNReal.ofReal (q r) ∂(volume.restrict (Ioo (0:ℝ) 1)).restrict (Icc (e n) (R n))) ≤ _
    rw [Measure.restrict_restrict measurableSet_Icc,inter_eq_left.2 (hsub n),← ofReal_integral_eq_lintegral_ofReal hqi hqnn]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (heR n)]
    exact radial_green_annulus (he n) (heR n) (hR n) hd hc hA hLc hL hm
  have helim : Tendsto e atTop (𝓝 0) := by
    simpa only [zero_div,e] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  have hRlim : Tendsto R atTop (𝓝 1) := by
    simpa only [sub_zero,R] using tendsto_const_nhds.sub helim
  have hlim (r : ℝ) (hr : r ∈ Ioo (0:ℝ) 1) :
      Tendsto (fun n => f n r) atTop (𝓝 (ENNReal.ofReal (Real.log (1/r)*(-r*L r)))) := by
    have hevent : ∀ᶠ n in atTop, r ∈ Icc (e n) (R n) := by
      filter_upwards [helim.eventually_lt_const hr.1,hRlim.eventually_const_lt hr.2] with n hn hn'
      exact ⟨hn.le,hn'.le⟩
    have ht := ENNReal.tendsto_ofReal (((hRlim.div_const r).log (div_ne_zero one_ne_zero (ne_of_gt hr.1))).mul_const (-r*L r))
    apply ht.congr'
    filter_upwards [hevent] with n hn
    exact (indicator_of_mem hn (fun r => ENNReal.ofReal (Real.log (R n/r)*(-r*L r)))).symm
  calc
    _ = ∫⁻ r, liminf (fun n => f n r) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact (hlim r hr).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ r, f n r ∂μ) atTop := lintegral_liminf_le' hfm
    _ ≤ _ := liminf_le_of_frequently_le (Eventually.frequently (Eventually.of_forall hbound))

lemma superharmonic_radial_green {u : ℂ → ℝ} {M : ℝ}
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hb : ∀ z ∈ ball (0:ℂ) 1, 0 ≤ u z ∧ u z ≤ M)
    (hΔ : ∀ z ∈ ball (0:ℂ) 1, Laplacian.laplacian u z ≤ 0) :
    (∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal (Real.log (1/r)*(-r*circleLMean u r))) ≤
      ENNReal.ofReal (2*Real.pi*M) := by
  have hrad (r : ℝ) (hr : r ∈ Ico (0:ℝ) 1) : |r| < 1 := by rw [abs_of_nonneg hr.1]; exact hr.2
  have hθc (r : ℝ) (hr : r ∈ Ico (0:ℝ) 1) : Continuous (fun θ => u (r • circleMap 0 1 θ)) :=
    continuousOn_univ.1 (hu.continuousOn.comp ((continuous_circleMap 0 1).const_smul r).continuousOn
      (fun θ _ => radial_mem (hrad r hr) θ))
  apply radial_green_integral (m := circleMean u) (d := circleDMean u)
  · intro r hr
    exact (circle_means_derivatives hu (hrad r hr)).1
  · intro r hr
    exact (circle_means_derivatives hu (hrad r hr)).2.continuousAt.continuousWithinAt
  · intro r hr
    exact weighted_circle_derivative hu hr.1 hr.2
  · exact (circle_lmean_continuous hu).mono (fun r hr => ⟨by linarith [hr.1],hr.2⟩)
  · intro r hr
    have hh := intervalIntegral.integral_nonneg (μ := volume) (neg_le_self Real.pi_pos.le)
      (f := fun θ => -Laplacian.laplacian u (r • circleMap 0 1 θ))
      (fun θ _ => neg_nonneg.2 (hΔ _ (radial_mem (by rw [abs_of_pos hr.1]; exact hr.2) θ)))
    rw [intervalIntegral.integral_neg] at hh
    exact neg_nonneg.1 hh
  · intro r hr
    constructor
    · apply intervalIntegral.integral_nonneg (neg_le_self Real.pi_pos.le)
      intro θ _
      exact (hb _ (radial_mem (hrad r hr) θ)).1
    · have hi := intervalIntegral.integral_mono_on (μ := volume) (neg_le_self Real.pi_pos.le)
        ((hθc r hr).intervalIntegrable _ _) (intervalIntegrable_const (c := M))
        (fun θ _ => (hb _ (radial_mem (hrad r hr) θ)).2)
      change circleMean u r ≤ _ at hi
      exact hi.trans_eq (by simp only [intervalIntegral.integral_const,smul_eq_mul]; ring)

theorem superharmonic_disk_green {u : ℂ → ℝ} {M : ℝ}
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hb : ∀ z ∈ ball (0:ℂ) 1, 0 ≤ u z ∧ u z ≤ M)
    (hΔ : ∀ z ∈ ball (0:ℂ) 1, Laplacian.laplacian u z ≤ 0) :
    (∫⁻ z in ball (0:ℂ) 1, ENNReal.ofReal (Real.log (1/‖z‖)*(-Laplacian.laplacian u z))) ≤
      ENNReal.ofReal (2*Real.pi*M) := by
  apply (polar_disk_lintegral_le _).trans
  have he : (∫⁻ r in Ioo (0:ℝ) 1, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal r * ENNReal.ofReal (Real.log (1/‖r • circleMap 0 1 θ‖)*
        (-Laplacian.laplacian u (r • circleMap 0 1 θ)))) =
      ∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal (Real.log (1/r)*(-r*circleLMean u r)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hrabs : |r| < 1 := by rw [abs_of_pos hr.1]; exact hr.2
    let q : ℝ → ℝ := fun θ => Real.log (1/r)*(-r*Laplacian.laplacian u (r • circleMap 0 1 θ))
    have hq : Continuous q := ((circle_laplacian_continuous hu hrabs).const_mul (-r)).const_mul _
    have hqi : IntegrableOn q (Ioc (-Real.pi) Real.pi) := (hq.intervalIntegrable _ _).1
    have hq0 : 0 ≤ᵐ[volume.restrict (Ioc (-Real.pi) Real.pi)] q := by
      filter_upwards with θ
      apply mul_nonneg
      · exact Real.log_nonneg ((one_le_div hr.1).2 hr.2.le)
      · exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 hr.1.le) (hΔ _ (radial_mem hrabs θ))
    have hqint : (∫ θ in -Real.pi..Real.pi, q θ) = Real.log (1/r)*(-r*circleLMean u r) := by
      dsimp only [q,circleLMean]
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
    calc
      _ = ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (q θ) := by
        apply lintegral_congr
        intro θ
        rw [radial_norm,abs_of_pos hr.1,← ENNReal.ofReal_mul hr.1.le]
        congr 1
        dsimp only [q]
        ring
      _ = ENNReal.ofReal (∫ θ in -Real.pi..Real.pi, q θ) := by
        rw [restrict_Ioo_eq_restrict_Ioc,intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le)]
        exact (ofReal_integral_eq_lintegral_ofReal hqi hq0).symm
      _ = _ := congrArg ENNReal.ofReal hqint
  rw [he]
  exact superharmonic_radial_green hu hb hΔ

end SLEExactGauge.Layer

end

end

section
noncomputable section
open Set Filter Metric Function
open scoped Topology
namespace SLEExactGauge.Layer

lemma univalent_not_locally_constant {F : ℂ → ℂ} (hi : InjOn F (ball 0 1))
    {c : ℂ} (hc : c ∈ ball (0:ℂ) 1) : ¬ ∀ᶠ z in 𝓝 c, F z = F c := by
  intro hh
  have he : ∀ᶠ z in 𝓝 c, z = c := by
    filter_upwards [hh,isOpen_ball.mem_nhds hc] with z hz hzD
    exact hi hzD hc hz
  have hb : ∀ᶠ z in 𝓝[≠] c, False := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z hz hne
    exact hne hz
  obtain ⟨z,hz⟩ := hb.exists
  exact hz

lemma univalent_punctured_derivative {F : ℂ → ℂ}
    (hf : DifferentiableOn ℂ F (ball 0 1)) (hi : InjOn F (ball 0 1))
    {c : ℂ} (hc : c ∈ ball (0:ℂ) 1) : ∀ᶠ z in 𝓝[≠] c, deriv F z ≠ 0 := by
  have ha := hf.analyticOnNhd isOpen_ball c hc
  apply ha.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left
  intro hz
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.1 (hz.and (isOpen_ball.mem_nhds hc))
  have hbd : ball c r ⊆ ball (0:ℂ) 1 := fun z hz => (hsub hz).2
  have hconst : ∀ᶠ z in 𝓝 c, F z = F c := by
    filter_upwards [ball_mem_nhds c hr] with z hz
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected
      (hf.mono hbd) (fun z hz => (hsub hz).1) hz (mem_ball_self hr)
  exact univalent_not_locally_constant hi hc hconst

theorem univalent_diskPair {F : ℂ → ℂ}
    (hf : DifferentiableOn ℂ F (ball 0 1)) (hi : InjOn F (ball 0 1)) :
    ∃ G : ℂ → ℂ, DiskPair (F '' ball 0 1) F G := by
  let U := F '' ball (0:ℂ) 1
  let G := invFunOn F (ball (0:ℂ) 1)
  have hl : ∀ z ∈ ball (0:ℂ) 1, G (F z) = z := hi.leftInvOn_invFunOn
  have hr : ∀ w ∈ U, F (G w) = w := (surjOn_image F (ball (0:ℂ) 1)).rightInvOn_invFunOn
  have hgmap : MapsTo G U (ball (0:ℂ) 1) := (surjOn_image F (ball (0:ℂ) 1)).mapsTo_invFunOn
  have hopen (c : ℂ) (hc : c ∈ ball (0:ℂ) 1) : 𝓝 (F c) ≤ map F (𝓝 c) :=
    ((hf.analyticOnNhd isOpen_ball c hc).eventually_constant_or_nhds_le_map_nhds).resolve_left
      (univalent_not_locally_constant hi hc)
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.2
    rintro w ⟨c,hc,rfl⟩
    apply hopen c hc
    change ∀ᶠ z in 𝓝 c, F z ∈ U
    filter_upwards [isOpen_ball.mem_nhds hc] with z hz
    exact mem_image_of_mem F hz
  have hGc (w : ℂ) (hw : w ∈ U) : ContinuousAt G w := by
    rcases hw with ⟨c,hc,rfl⟩
    rw [ContinuousAt,hl c hc]
    calc
      map G (𝓝 (F c)) ≤ map G (map F (𝓝 c)) := map_mono (hopen c hc)
      _ = map id (𝓝 c) := by
        rw [map_map]
        apply Filter.map_congr
        filter_upwards [isOpen_ball.mem_nhds hc] with z hz
        exact hl z hz
      _ = 𝓝 c := map_id
  have hgood (w : ℂ) (hw : w ∈ U) (hn : deriv F (G w) ≠ 0) : DifferentiableAt ℂ G w := by
    apply HasDerivAt.differentiableAt (f' := (deriv F (G w))⁻¹)
    apply HasDerivAt.of_local_left_inverse (hGc w hw)
      (hf.differentiableAt (isOpen_ball.mem_nhds (hgmap hw))).hasDerivAt hn
    filter_upwards [hU.mem_nhds hw] with y hy
    exact hr y hy
  have hGd (w : ℂ) (hw : w ∈ U) : DifferentiableAt ℂ G w := by
    have hc := hgmap hw
    have htn : Tendsto G (𝓝[≠] w) (𝓝[≠] G w) := by
      apply tendsto_nhdsWithin_iff.2
      refine ⟨(hGc w hw).tendsto.mono_left nhdsWithin_le_nhds,?_⟩
      filter_upwards [(show ∀ᶠ y in 𝓝 w, y ∈ U from hU.mem_nhds hw).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with y hy hne
      change G y ≠ G w
      intro hgy
      apply hne
      change y = w
      rw [← hr y hy,hgy,hr w hw]
    have hne := htn.eventually (univalent_punctured_derivative hf hi hc)
    apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ (hGc w hw)).differentiableAt
    filter_upwards [hne,(show ∀ᶠ y in 𝓝 w, y ∈ U from hU.mem_nhds hw).filter_mono nhdsWithin_le_nhds] with y hn hy
    exact hgood y hy hn
  exact ⟨G,hU,(fun z hz => mem_image_of_mem F hz),hgmap,hl,hr,hf,fun w hw => (hGd w hw).differentiableWithinAt⟩

end SLEExactGauge.Layer

end

end

end OAI
