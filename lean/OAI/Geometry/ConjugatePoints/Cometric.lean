import OAI.Geometry.ConjugatePoints.Basic

namespace OAI

noncomputable section

/-!
# Radial profiles, cometrics, and collar estimates.
-/

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.RadialProfile

def cut (r : ℝ) : ℝ := Real.smoothTransition (4*r-1)
def coordinate (L r : ℝ) : ℝ :=
  (1-cut r)*(r-L-1) + cut r*((r-Real.log 2)/Real.log 4)
def slope (L r : ℝ) : ℝ :=
  1-cut r + cut r / Real.log 4 + deriv cut r *
    (((r-Real.log 2)/Real.log 4) - (r-L-1))
lemma cut_smooth : ContDiff ℝ ∞ cut :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
lemma cut_zero {r : ℝ} (h : r ≤ 1/4) : cut r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
lemma cut_one {r : ℝ} (h : 1/2 ≤ r) : cut r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
lemma cut_nonneg (r : ℝ) : 0 ≤ cut r := Real.smoothTransition.nonneg _
lemma cut_le_one (r : ℝ) : cut r ≤ 1 := Real.smoothTransition.le_one _
lemma cut_mono : Monotone cut :=
  Real.smoothTransition.monotone.comp (fun _ _ h => by linarith)
lemma cut_deriv_nonneg (r : ℝ) : 0 ≤ deriv cut r := cut_mono.deriv_nonneg
lemma cut_deriv_eq_zero {r : ℝ} (h : r ∉ Icc (1/4:ℝ) (1/2)) : deriv cut r = 0 := by
  rcases not_and_or.mp h with h|h
  · have hr : r < 1/4 := lt_of_not_ge h
    have he : cut =ᶠ[nhds r] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds hr] with x hx
      exact cut_zero hx.le
    exact he.deriv_eq.trans (deriv_const r 0)
  · have hr : 1/2 < r := lt_of_not_ge h
    have he : cut =ᶠ[nhds r] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      exact cut_one hx.le
    exact he.deriv_eq.trans (deriv_const r 1)
lemma log_bounds : 1/2 < Real.log 2 ∧ 1 < Real.log 4 ∧ Real.log 2 < 1 ∧ Real.log 4 < 2 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith
lemma coordinate_smooth (L : ℝ) : ContDiff ℝ ∞ (coordinate L) :=
  ((contDiff_const.sub cut_smooth).mul ((contDiff_id.sub contDiff_const).sub contDiff_const)).add
    (cut_smooth.mul ((contDiff_id.sub contDiff_const).div_const _))
lemma coordinate_deriv (L r : ℝ) : HasDerivAt (coordinate L) (slope L r) r := by
  have h := (((hasDerivAt_const r 1).sub (cut_smooth.differentiable (by simp) r).hasDerivAt).mul
    (((hasDerivAt_id r).sub_const L).sub_const 1)).add
    (((cut_smooth.differentiable (by simp) r).hasDerivAt).mul
      (((hasDerivAt_id r).sub_const (Real.log 2)).div_const (Real.log 4)))
  convert! h using 1
  simp only [slope, id_eq, Pi.sub_apply]
  ring
lemma coordinate_left {L r : ℝ} (h : r ≤ 1/4) : coordinate L r = r-L-1 := by
  simp [coordinate,cut_zero h]
lemma coordinate_right {L r : ℝ} (h : 1/2 ≤ r) :
    coordinate L r = (r-Real.log 2)/Real.log 4 := by
  simp [coordinate,cut_one h]
lemma transition_difference_pos {L r : ℝ} (hL : 4 ≤ L) (hr : r ∈ Icc (1/4:ℝ) (1/2)) :
    0 < (r-Real.log 2)/Real.log 4 - (r-L-1) := by
  have hb := log_bounds
  have hd : -(1:ℝ) < (r-Real.log 2)/Real.log 4 := by
    apply (lt_div_iff₀ (by linarith : 0 < Real.log 4)).mpr
    nlinarith [hr.1,hr.2]
  linarith [hr.2]
lemma slope_pos {L : ℝ} (hL : 4 ≤ L) (r : ℝ) : 0 < slope L r := by
  have hb := log_bounds
  have hbase : 0 < 1-cut r + cut r / Real.log 4 := by
    by_cases h : cut r = 0
    · simp [h]
    · have hp : 0 < cut r := lt_of_le_of_ne (cut_nonneg r) (Ne.symm h)
      exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr (cut_le_one r))
        (div_pos hp (by linarith))
  unfold slope
  by_cases h : r ∈ Icc (1/4:ℝ) (1/2)
  · exact add_pos_of_pos_of_nonneg hbase
      (mul_nonneg (cut_deriv_nonneg r) (transition_difference_pos hL h).le)
  · rw [cut_deriv_eq_zero h,zero_mul,add_zero]
    exact hbase
lemma coordinate_strictMono {L : ℝ} (hL : 4 ≤ L) : StrictMono (coordinate L) := by
  apply strictMono_of_deriv_pos
  intro r
  rw [(coordinate_deriv L r).deriv]
  exact slope_pos hL r

lemma coordinate_neck {L y : ℝ} (hy : 2 ≤ y) :
    coordinate L (Real.log y) = (Real.log y-Real.log 2)/Real.log 4 := by
  apply coordinate_right
  have hm : Real.log 2 ≤ Real.log y := Real.strictMonoOn_log.monotoneOn
    (by norm_num : (2:ℝ) ∈ Ioi 0) (show y ∈ Ioi (0:ℝ) by change 0 < y; linarith) hy
  linarith [log_bounds.1]
lemma coordinate_flip {L K y : ℝ} (hy : y ∈ Icc (2:ℝ) 8) :
    coordinate K (Real.log (16/y)) = 1-coordinate L (Real.log y) := by
  have hp : 0 < y := by linarith [hy.1]
  have hh : (2:ℝ) ≤ 16/y := (le_div_iff₀ hp).mpr (by linarith [hy.2])
  rw [coordinate_neck hh,coordinate_neck hy.1,Real.log_div (by norm_num) hp.ne']
  have h16 : Real.log 16 = 2*Real.log 4 := by
    rw [show (16:ℝ) = 4^2 by norm_num,Real.log_pow]; norm_num
  have h4 : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]; norm_num
  rw [h16]
  field_simp
  linarith
end ThreeManifold.RadialProfile
end

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric

def a (u : ℝ) : ℝ := expNegInvGlue ((2 : ℝ) / 3 - u)

def A (u : ℝ) : ℝ := ∫ y in (0 : ℝ)..u, a y

def χ (t : ℝ) : ℝ := Real.smoothTransition (6 * (t - 5 / 12))

lemma a_formula (u : ℝ) :
    a u = if u < 2 / 3 then Real.exp (-1 / (2 / 3 - u)) else 0 := by
  unfold a expNegInvGlue
  split_ifs <;> (try congr 1) <;> (try simp_all only [not_lt, not_le]) <;>
    (first | linarith | simp [div_eq_mul_inv])

@[fun_prop] lemma a_smooth : ContDiff ℝ ∞ a :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)

lemma a_nonneg (u : ℝ) : 0 ≤ a u := expNegInvGlue.nonneg _

lemma a_pos {u : ℝ} (hu : u < 2 / 3) : 0 < a u :=
  expNegInvGlue.pos_of_pos (by linarith)

lemma a_eq_zero {u : ℝ} (hu : 2 / 3 ≤ u) : a u = 0 :=
  expNegInvGlue.zero_of_nonpos (by linarith)

lemma a_lt_one (u : ℝ) : a u < 1 := by
  rw [a_formula]
  split_ifs with hu
  · exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) (by linarith))
  · norm_num

lemma a_antitone : Antitone a := by
  intro x y hxy
  exact expNegInvGlue.monotone (by linarith)

lemma a_zero : a 0 = Real.exp (-(3 : ℝ) / 2) := by norm_num [a_formula]

lemma a_eighth_ratio : a (1 / 8) / a 0 = Real.exp (-(9 : ℝ) / 26) := by
  rw [a_zero, a_formula]
  norm_num
  rw [← Real.exp_sub]
  congr 1
  norm_num

lemma a_hasDerivAt (u : ℝ) :
    HasDerivAt a (-a u / (2 / 3 - u) ^ 2) u := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) (2 / 3 - u)
  simp only [Polynomial.eval_one, one_mul, Polynomial.derivative_one, sub_zero,
    mul_one, Polynomial.eval_pow, Polynomial.eval_X] at h
  have hcomp := h.comp u ((hasDerivAt_const u (2 / 3)).sub (hasDerivAt_id u))
  convert! hcomp using 1
  simp [a, div_eq_mul_inv, inv_pow, mul_comm]

lemma a_deriv (u : ℝ) : deriv a u = -a u / (2 / 3 - u) ^ 2 :=
  (a_hasDerivAt u).deriv

lemma a_deriv_nonpos (u : ℝ) : deriv a u ≤ 0 := by
  rw [a_deriv]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (a_nonneg u)) (sq_nonneg _)

lemma a_sq_le_neg_deriv {u : ℝ} (hu : u ∈ Icc 0 1) :
    a u ^ 2 ≤ -deriv a u := by
  by_cases hcut : u < 2 / 3
  · have hx : 0 < 2 / 3 - u := by linarith
    have hxupper : (2 / 3 - u) ^ 2 ≤ (1 : ℝ) := by nlinarith [hu.1]
    have ha := a_nonneg u
    have ha' := (a_lt_one u).le
    rw [a_deriv, neg_div, neg_neg]
    apply (le_div_iff₀ (sq_pos_of_pos hx)).mpr
    calc
      a u ^ 2 * (2 / 3 - u) ^ 2 ≤ a u ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hxupper (sq_nonneg _)
      _ ≤ a u := by nlinarith
  · rw [a_deriv, a_eq_zero (le_of_not_gt hcut)]
    simp

private lemma sq_le_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 2 ≤ Real.exp y := by
  have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ y / 2 by linarith)
  have he : y ≤ Real.exp (y / 2) := by nlinarith [sq_nonneg (y - 2)]
  calc
    y ^ 2 ≤ Real.exp (y / 2) ^ 2 :=
      (sq_le_sq₀ hy (Real.exp_pos _).le).mpr he
    _ = Real.exp y := by rw [pow_two, ← Real.exp_add]; congr 1; ring

lemma a_deriv_abs_le_one (u : ℝ) : |deriv a u| ≤ 1 := by
  rw [abs_of_nonpos (a_deriv_nonpos u)]
  by_cases hcut : u < 2 / 3
  · have hx : 0 < 2 / 3 - u := by linarith
    have hy := sq_le_exp (inv_nonneg.mpr hx.le)
    have h := (div_le_one (Real.exp_pos (2 / 3 - u)⁻¹)).mpr hy
    rw [a_deriv, a_formula, ite_eq_left hcut]
    simpa [Real.exp_neg, div_eq_mul_inv, inv_pow, mul_comm] using h
  · rw [a_deriv, a_eq_zero (le_of_not_gt hcut)]
    simp

lemma neg_a_deriv_hasDerivAt {u : ℝ} (hu : u < 2 / 3) :
    HasDerivAt (fun x => -deriv a x)
      (a u * (2 * (2 / 3 - u) - 1) / (2 / 3 - u) ^ 4) u := by
  have hx : 2 / 3 - u ≠ 0 := by linarith
  have hs := ((hasDerivAt_const u ((2 : ℝ) / 3)).sub (hasDerivAt_id u)).pow 2
  have h := (a_hasDerivAt u).div hs (pow_ne_zero 2 hx)
  convert! h using 1
  · funext x
    simp only [a_deriv, Pi.div_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
    ring
  · dsimp only [Pi.pow_apply, Pi.sub_apply, id_eq]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, sub_zero, zero_sub]
    field_simp [hx]
    ring

lemma neg_a_deriv_antitone_mid :
    AntitoneOn (fun u => -deriv a u) (Icc (5 / 12) (7 / 12)) := by
  have hc : ContDiff ℝ ∞ (fun u => -deriv a u) :=
    (contDiff_infty_iff_deriv.mp a_smooth).2.neg
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hc.continuous.continuousOn
    (hc.differentiable (by simp)).differentiableOn ?_
  intro u hu
  rw [interior_Icc] at hu
  have hcut : u < 2 / 3 := by linarith [hu.2]
  rw [(neg_a_deriv_hasDerivAt hcut).deriv]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (a_nonneg u) (by linarith [hu.1]))
    (by positivity)

lemma a_slope_lower {u : ℝ} (hu : u ∈ Icc (5 / 12) (7 / 12)) :
    144 * Real.exp (-12) ≤ -deriv a u := by
  have h := neg_a_deriv_antitone_mid hu (show (7 / 12 : ℝ) ∈ Icc (5 / 12) (7 / 12)
    by norm_num) hu.2
  have he : -deriv a (7 / 12) = 144 * Real.exp (-12) := by
    rw [a_deriv, a_formula]
    norm_num
    ring
  dsimp only at h
  rwa [he] at h

lemma A_hasDerivAt (u : ℝ) : HasDerivAt A (a u) u :=
  a_smooth.continuous.integral_hasStrictDerivAt 0 u |>.hasDerivAt

lemma A_deriv : deriv A = a := funext fun u => (A_hasDerivAt u).deriv

@[fun_prop] lemma A_smooth : ContDiff ℝ ∞ A := by
  apply contDiff_infty_iff_deriv.mpr
  exact ⟨fun u => (A_hasDerivAt u).differentiableAt, A_deriv ▸ a_smooth⟩

lemma A_zero : A 0 = 0 := by simp [A]

lemma A_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ A u :=
  intervalIntegral.integral_nonneg hu (fun x _ => a_nonneg x)

lemma A_le {u : ℝ} (hu : 0 ≤ u) : A u ≤ u := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hu
    (a_smooth.continuous.intervalIntegrable 0 u) (continuous_const.intervalIntegrable 0 u)
    (fun x (_hx : x ∈ Icc 0 u) => (a_lt_one x).le)
  simpa [A] using h

lemma A_plateau {u v : ℝ} (hu : 2 / 3 ≤ u) (hv : 2 / 3 ≤ v) : A u = A v := by
  have hi : (∫ x in u..v, a x) = 0 := by
    calc
      (∫ x in u..v, a x) = ∫ _x in u..v, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact a_eq_zero (le_trans (le_min hu hv) hx.1)
      _ = 0 := by simp
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (a_smooth.continuous.intervalIntegrable 0 u)
    (a_smooth.continuous.intervalIntegrable u v)
  simpa [hi, A] using h

@[fun_prop] lemma χ_smooth : ContDiff ℝ ∞ χ :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))

lemma χ_nonneg (t : ℝ) : 0 ≤ χ t := Real.smoothTransition.nonneg _
lemma χ_le_one (t : ℝ) : χ t ≤ 1 := Real.smoothTransition.le_one _

lemma χ_monotone : Monotone χ := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

lemma χ_eq_zero {t : ℝ} (ht : t ≤ 5 / 12) : χ t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma χ_eq_one {t : ℝ} (ht : 7 / 12 ≤ t) : χ t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma χ_eventually_zero {t : ℝ} (ht : t < 5 / 12) :
    χ =ᶠ[𝓝 t] fun _ => 0 := by
  filter_upwards [gt_mem_nhds ht] with x hx
  exact χ_eq_zero hx.le

lemma χ_eventually_one {t : ℝ} (ht : 7 / 12 < t) :
    χ =ᶠ[𝓝 t] fun _ => 1 := by
  filter_upwards [lt_mem_nhds ht] with x hx
  exact χ_eq_one hx.le

lemma χ_deriv_left {t : ℝ} (ht : t < 5 / 12) : deriv χ t = 0 := by
  simpa using (χ_eventually_zero ht).deriv_eq

lemma χ_deriv_right {t : ℝ} (ht : 7 / 12 < t) : deriv χ t = 0 := by
  simpa using (χ_eventually_one ht).deriv_eq

lemma χ_deriv2_left {t : ℝ} (ht : t < 5 / 12) : deriv (deriv χ) t = 0 := by
  simpa using (χ_eventually_zero ht).deriv.deriv_eq

lemma χ_deriv2_right {t : ℝ} (ht : 7 / 12 < t) : deriv (deriv χ) t = 0 := by
  simpa using (χ_eventually_one ht).deriv.deriv_eq

lemma χ_deriv_smooth : ContDiff ℝ ∞ (deriv χ) :=
  (contDiff_infty_iff_deriv.mp χ_smooth).2

lemma χ_deriv2_smooth : ContDiff ℝ ∞ (deriv (deriv χ)) :=
  (contDiff_infty_iff_deriv.mp χ_deriv_smooth).2

lemma χ_derivative_bounds : ∃ K1 K2 : ℝ, 1 ≤ K1 ∧ 1 ≤ K2 ∧
    (∀ t, |deriv χ t| ≤ K1) ∧ (∀ t, |deriv (deriv χ) t| ≤ K2) := by
  obtain ⟨k1, hk1⟩ := (isCompact_Icc : IsCompact (Icc (5 / 12 : ℝ) (7 / 12))).exists_bound_of_continuousOn
    χ_deriv_smooth.continuous.continuousOn
  obtain ⟨k2, hk2⟩ := (isCompact_Icc : IsCompact (Icc (5 / 12 : ℝ) (7 / 12))).exists_bound_of_continuousOn
    χ_deriv2_smooth.continuous.continuousOn
  refine ⟨max 1 k1, max 1 k2, le_max_left _ _, le_max_left _ _, ?_, ?_⟩
  · intro t
    rcases lt_or_ge t (5 / 12) with ht | ht
    · rw [χ_deriv_left ht, abs_zero]
      exact le_trans zero_le_one (le_max_left _ _)
    rcases le_or_gt t (7 / 12) with ht' | ht'
    · exact le_trans (by simpa only [Real.norm_eq_abs] using hk1 t ⟨ht, ht'⟩) (le_max_right _ _)
    · rw [χ_deriv_right ht', abs_zero]
      exact le_trans zero_le_one (le_max_left _ _)
  · intro t
    rcases lt_or_ge t (5 / 12) with ht | ht
    · rw [χ_deriv2_left ht, abs_zero]
      exact le_trans zero_le_one (le_max_left _ _)
    rcases le_or_gt t (7 / 12) with ht' | ht'
    · exact le_trans (by simpa only [Real.norm_eq_abs] using hk2 t ⟨ht, ht'⟩) (le_max_right _ _)
    · rw [χ_deriv2_right ht', abs_zero]
      exact le_trans zero_le_one (le_max_left _ _)

end ThreeManifold.Cometric

open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.Collar
open Cometric

def lam (t : ℝ) : ℝ := Real.smoothTransition (2 * t + 3 / 2)
@[fun_prop] lemma lam_smooth : ContDiff ℝ ∞ lam := by unfold lam; fun_prop
lemma lam_nonneg (t : ℝ) : 0 ≤ lam t := Real.smoothTransition.nonneg _
lemma lam_le_one (t : ℝ) : lam t ≤ 1 := Real.smoothTransition.le_one _
lemma lam_monotone : Monotone lam := fun _ _ h => Real.smoothTransition.monotone (by linarith)
lemma lam_zero {t : ℝ} (ht : t ≤ -3 / 4) : lam t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
lemma lam_one {t : ℝ} (ht : -1 / 4 ≤ t) : lam t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
lemma A_le_zero {t : ℝ} (ht : t ≤ 0) : A t ≤ 0 := by
  rw [A, intervalIntegral.integral_symm]
  exact neg_nonpos.mpr (intervalIntegral.integral_nonneg (by simpa using ht)
    (fun u _ => a_nonneg u))
lemma A_ge_self {t : ℝ} (ht : t ≤ 0) : t ≤ A t := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht
    (a_smooth.continuous.intervalIntegrable t 0)
    (continuous_const.intervalIntegrable t 0) (fun u _ => (a_lt_one u).le)
  simp only [intervalIntegral.integral_const, zero_sub, smul_eq_mul, mul_one] at h
  rw [A, intervalIntegral.integral_symm]
  linarith
lemma A_ge_neg_one {t : ℝ} (ht : -1 ≤ t) : -1 ≤ A t := by
  rcases le_total t 0 with h | h
  · exact ht.trans (A_ge_self h)
  · exact (by norm_num : (-1 : ℝ) ≤ 0).trans (A_nonneg h)

def denom (δ t : ℝ) : ℝ := 1 + δ * A t
def rate (δ t : ℝ) : ℝ := δ * a t / (2 * denom δ t)
def k (δ t : ℝ) : ℝ := 1 - lam t + lam t * rate δ t
def ell (δ t : ℝ) : ℝ := Real.exp (-(∫ u in (0 : ℝ)..t, k δ u))

lemma denom_lower {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : -1 ≤ t) :
    1 / 2 ≤ denom δ t := by
  have h := mul_le_mul_of_nonneg_left (A_ge_neg_one ht) hδ.1
  dsimp [denom]; nlinarith [hδ.2]
lemma denom_pos {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : -1 ≤ t) :
    0 < denom δ t := lt_of_lt_of_le (by norm_num) (denom_lower hδ ht)
@[fun_prop] lemma denom_smooth (δ : ℝ) : ContDiff ℝ ∞ (denom δ) := by
  unfold denom; fun_prop
lemma denom_hasDerivAt (δ t : ℝ) : HasDerivAt (denom δ) (δ * a t) t :=
  ((A_hasDerivAt t).const_mul δ).const_add 1
lemma rate_contDiffAt {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : -1 ≤ t) :
    ContDiffAt ℝ ∞ (rate δ) t := by
  apply ContDiffAt.div (contDiffAt_const.mul a_smooth.contDiffAt)
    (contDiffAt_const.mul (denom_smooth δ).contDiffAt)
  exact mul_ne_zero (by norm_num) (ne_of_gt (denom_pos hδ ht))
lemma rate_pos {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1 / 2)) (ht : t ∈ Icc (-1) 0) :
    0 < rate δ t :=
  div_pos (mul_pos hδ.1 (a_pos (by linarith [ht.2])))
    (mul_pos (by norm_num) (denom_pos ⟨hδ.1.le, hδ.2⟩ ht.1))
lemma rate_le_delta {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : -1 ≤ t) :
    rate δ t ≤ δ := by
  apply (div_le_iff₀ (mul_pos (by norm_num) (denom_pos hδ ht))).mpr
  have h := denom_lower hδ ht
  have ha := mul_le_mul_of_nonneg_left (a_lt_one t).le hδ.1
  nlinarith [mul_nonneg hδ.1 (show 0 ≤ 2 * denom δ t - 1 by linarith)]
lemma k_eq_one {δ t : ℝ} (ht : t ≤ -3 / 4) : k δ t = 1 := by
  simp [k, lam_zero ht]
lemma k_eq_rate {δ t : ℝ} (ht : -1 / 4 ≤ t) : k δ t = rate δ t := by
  simp [k, lam_one ht]
lemma k_smooth {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) : ContDiff ℝ ∞ (k δ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t < -3 / 4
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact k_eq_one hu.le
  · have ht' : -1 ≤ t := by linarith
    exact (contDiffAt_const.sub lam_smooth.contDiffAt).add
      (lam_smooth.contDiffAt.mul (rate_contDiffAt hδ ht'))
lemma k_positive {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1 / 2)) (ht : t ∈ Icc (-1) 0) :
    0 < k δ t := by
  have hr := rate_pos hδ ht
  have hl := lam_nonneg t
  have hu := lam_le_one t
  by_cases hl0 : lam t = 0
  · simp [k, hl0]
  · have hp := mul_pos (lt_of_le_of_ne hl (Ne.symm hl0)) hr
    dsimp [k]; linarith
lemma rate_hasDerivAt {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : -1 ≤ t) :
    HasDerivAt (rate δ)
      (δ * (deriv a t * denom δ t - δ * a t ^ 2) / (2 * denom δ t ^ 2)) t := by
  have hd : denom δ t ≠ 0 := ne_of_gt (denom_pos hδ ht)
  convert! (((a_hasDerivAt t).const_mul δ).div
    ((denom_hasDerivAt δ t).const_mul 2) (mul_ne_zero (by norm_num) hd)) using 1
  rw [← (a_hasDerivAt t).deriv]
  field_simp
lemma rate_deriv_neg {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1 / 2)) (ht : t ∈ Icc (-1) 0) :
    deriv (rate δ) t < 0 := by
  rw [(rate_hasDerivAt ⟨hδ.1.le, hδ.2⟩ ht.1).deriv]
  have hD := denom_pos ⟨hδ.1.le, hδ.2⟩ ht.1
  apply div_neg_of_neg_of_pos _ (mul_pos (by norm_num) (sq_pos_of_pos hD))
  apply mul_neg_of_pos_of_neg hδ.1
  have h1 := mul_nonpos_of_nonpos_of_nonneg (a_deriv_nonpos t) hD.le
  have h2 := mul_pos hδ.1 (sq_pos_of_pos (a_pos (u := t) (by linarith [ht.2])))
  linarith
lemma k_hasDerivAt {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    HasDerivAt (k δ) (deriv lam t * (rate δ t - 1) + lam t * deriv (rate δ) t) t := by
  by_cases ht : t < -3 / 4
  · have he : k δ =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds ht] with u hu using k_eq_one hu.le
    have hl : lam =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with u hu using lam_zero hu.le
    rw [hl.deriv_eq, deriv_const, lam_zero ht.le]
    simpa using (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq he
  · have ht' : -1 ≤ t := by linarith
    have hl := lam_smooth.differentiable (by simp) t
    have hr := (rate_contDiffAt hδ ht').differentiableAt (by simp)
    convert! (hl.hasDerivAt.const_sub 1).add (hl.hasDerivAt.mul hr.hasDerivAt) using 1
    ring
lemma k_deriv_nonpos {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1 / 2)) (ht : t ∈ Icc (-1) 0) :
    deriv (k δ) t ≤ 0 := by
  rw [(k_hasDerivAt (t := t) ⟨hδ.1.le, hδ.2⟩).deriv]
  apply add_nonpos
  · apply mul_nonpos_of_nonneg_of_nonpos lam_monotone.deriv_nonneg
    have h := rate_le_delta ⟨hδ.1.le, hδ.2⟩ ht.1
    linarith [hδ.2]
  · exact mul_nonpos_of_nonneg_of_nonpos (lam_nonneg t) (rate_deriv_neg hδ ht).le
lemma ell_pos (δ t : ℝ) : 0 < ell δ t := Real.exp_pos _
@[simp] lemma ell_zero (δ : ℝ) : ell δ 0 = 1 := by simp [ell]
lemma integral_k_smooth {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    ContDiff ℝ ∞ (fun t => ∫ u in (0 : ℝ)..t, k δ u) := by
  apply contDiff_infty_iff_deriv.mpr
  have hd (t : ℝ) := (k_smooth hδ).continuous.integral_hasStrictDerivAt 0 t |>.hasDerivAt
  refine ⟨fun t => (hd t).differentiableAt, ?_⟩
  convert! k_smooth hδ using 1
  exact funext fun t => (hd t).deriv
lemma ell_smooth {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) : ContDiff ℝ ∞ (ell δ) :=
  (integral_k_smooth hδ).neg.exp
lemma ell_hasDerivAt {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    HasDerivAt (ell δ) (-k δ t * ell δ t) t := by
  have hd := (k_smooth hδ).continuous.integral_hasStrictDerivAt 0 t |>.hasDerivAt
  convert! hd.neg.exp using 1
  dsimp [ell]
  ring
lemma ell_deriv {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    deriv (ell δ) = fun t => -k δ t * ell δ t :=
  funext fun _ => (ell_hasDerivAt hδ).deriv
lemma ell_second {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    deriv (deriv (ell δ)) t = (k δ t ^ 2 - deriv (k δ) t) * ell δ t := by
  rw [ell_deriv hδ]
  have hk := ((k_smooth hδ).differentiable (by simp) t).hasDerivAt
  convert! (hk.neg.mul (ell_hasDerivAt hδ)).deriv using 1
  dsimp
  ring
lemma ell_strictConvex_second {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1 / 2))
    (ht : t ∈ Icc (-1) 0) : 0 < deriv (deriv (ell δ)) t := by
  rw [ell_second ⟨hδ.1.le, hδ.2⟩]
  apply mul_pos _ (ell_pos δ t)
  have h1 := k_deriv_nonpos hδ ht
  have h2 := sq_pos_of_pos (k_positive hδ ht)
  linarith

lemma squared_end_hasDerivAt {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    (ht : -1 / 4 ≤ t) :
    HasDerivAt (fun u => (ell δ u)^2 * denom δ u) 0 t := by
  have hD := ne_of_gt (denom_pos hδ (by linarith : -1 ≤ t))
  convert! ((ell_hasDerivAt hδ).pow 2).mul (denom_hasDerivAt δ t) using 1
  rw [k_eq_rate ht]
  dsimp [rate]
  field_simp; ring
lemma squared_end_constant {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    (ht : -1 / 4 < t) : (ell δ t)^2 * denom δ t = 1 := by
  have hd (u : ℝ) (hu : u ∈ Ioi (-1 / 4)) := squared_end_hasDerivAt hδ hu.le
  have he := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun u hu => (hd u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hd u hu).deriv) ht (by norm_num : (0 : ℝ) ∈ Ioi (-1 / 4))
  simpa [denom, A_zero] using he

lemma ell_end_germ {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : -1 / 4 < t) :
    ell δ t = (Real.sqrt (1 + δ * A t))⁻¹ := by
  have hD := denom_pos hδ (by linarith : -1 ≤ t)
  have hs := Real.sq_sqrt hD.le
  have he := squared_end_constant hδ ht
  have hp := ell_pos δ t
  have hspos := Real.sqrt_pos.mpr hD
  rw [inv_eq_one_div]
  apply (eq_div_iff hspos.ne').mpr
  change ell δ t * Real.sqrt (denom δ t) = 1
  nlinarith [mul_pos hp hspos, sq_nonneg (ell δ t * Real.sqrt (denom δ t) - 1)]

lemma ell_cusp_germ {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ≤ -3 / 4) :
    ell δ t = ell δ (-1) * Real.exp (-(t + 1)) := by
  have hi : (∫ u in (-1 : ℝ)..t, k δ u) = t + 1 := by
    calc
      _ = ∫ _ in (-1 : ℝ)..t, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact k_eq_one (hu.2.trans (max_le (by norm_num) ht))
      _ = t + 1 := by simp
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    ((k_smooth hδ).continuous.intervalIntegrable 0 (-1))
    ((k_smooth hδ).continuous.intervalIntegrable (-1) t)
  rw [hi] at he
  change Real.exp (-(∫ u in (0 : ℝ)..t, k δ u)) = _
  rw [← he, neg_add, Real.exp_add]
  rfl

theorem exact_convex_collar {δ : ℝ} (hδ : δ ∈ Ioc 0 (1 / 2)) :
    ContDiff ℝ ∞ (ell δ) ∧ (∀ t, 0 < ell δ t) ∧ ell δ 0 = 1 ∧
    (∀ t ∈ Icc (-1 : ℝ) 0, 0 < deriv (deriv (ell δ)) t) ∧
    (∀ t ∈ Ioi (-1 / 4 : ℝ), ell δ t = (Real.sqrt (1 + δ * A t))⁻¹) ∧
    (∀ t ∈ Iio (-3 / 4 : ℝ), ell δ t = ell δ (-1) * Real.exp (-(t + 1))) := by
  refine ⟨ell_smooth ⟨hδ.1.le, hδ.2⟩, ell_pos δ, ell_zero δ,
    fun _ ht => ell_strictConvex_second hδ ht,
    fun _ ht => ell_end_germ ⟨hδ.1.le, hδ.2⟩ ht,
    fun _ ht => ell_cusp_germ ⟨hδ.1.le, hδ.2⟩ ht.le⟩

end ThreeManifold.Collar

end

end OAI
