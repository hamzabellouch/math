import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ProfileBounds

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma continuousOn_gain : ContinuousOn gain (Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) := by
  have hc := continuousOn_critical (a := (51 / 50 : ℝ)) (b := (81 / 50 : ℝ)) (by norm_num)
  have hP := continuousOn_P (a := (51 / 50 : ℝ)) (b := (81 / 50 : ℝ)) (by norm_num)
  have hQ := (contDiff_Q (n := 0)).continuous.continuousOn (s := Icc (51 / 50 : ℝ) (81 / 50 : ℝ))
  have hformula : ContinuousOn (fun h ↦ min (C₀ h * dm ^ 3)
      (ell * ((P h - critical ell (C₀ h) (P h) (Q h)) / Q h) ^ 2 +
        C₀ h * critical ell (C₀ h) (P h) (Q h) ^ 3)) (Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) := by
    apply (continuous_C₀.continuousOn.mul continuousOn_const).inf
    exact (continuousOn_const.mul (((hP.sub hc).div hQ (fun h _ ↦ (Q_positive h).ne')).pow 2)).add
      (continuous_C₀.continuousOn.mul (hc.pow 3))
  exact hformula.congr (fun h hh ↦ gain_formula hh)

lemma active_upper_argument_jets {h y : ℝ} {U : ℝ → ℝ}
    (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) (hy : 0 ≤ y)
    (hU : UpperSupport u U h)
    (hU'lo : -(49 / 100 : ℝ) ≤ deriv U h) (hU'hi : deriv U h ≤ 0)
    (hU''hi : deriv (deriv U) h ≤ 7 / 10)
    (hw : 0 < U h - 1 + R h - Q h * y) :
    let w := fun H ↦ U H - 1 + R H - Q H * y;
    -(1 / 2 : ℝ) ≤ deriv w h ∧ deriv w h ≤ 17 / 50 ∧ deriv (deriv w) h ≤ 4 / 5 := by
  have hh0 : 0 < h := by linarith [hh.1]
  have hh1 : (1 : ℝ) ≤ h := by linarith [hh.1]
  have hsq : (1 : ℝ) ≤ h ^ 2 := by nlinarith
  have hQy0 : 0 ≤ Q h * y := mul_nonneg (Q_positive h).le hy
  have hQy : Q h * y ≤ 9 / 25 := by
    rw [hU.contact] at hw
    have := gain_P_lt hh
    change u h - 1 + R h < _ at this
    linarith
  have hlog := Q_log_bounds hh0
  have hlog1 : 2 * h / QRad h ≤ 1 / 2 := hlog.2.1.trans
    ((div_le_div_iff₀ (by positivity : 0 < 2 * h) (by norm_num : (0 : ℝ) < 2)).2 (by linarith))
  have hlog2 : -(1 / 4 : ℝ) ≤ (2 * Real.pi - 4 * h ^ 2) / QRad h ^ 2 := by
    apply le_trans _ hlog.2.2
    have hb : (1 : ℝ) / (4 * h ^ 2) ≤ 1 / 4 :=
      (div_le_div_iff₀ (by positivity : 0 < 4 * h ^ 2) (by norm_num : (0 : ℝ) < 4)).2 (by linarith)
    linarith
  have hQ'0 : 0 ≤ deriv Q h * y := by
    rw [deriv_Q_eq hh0]
    exact mul_nonneg (mul_nonneg (Q_positive h).le hlog.1.le) hy
  have hQ' : deriv Q h * y ≤ 9 / 50 := by
    rw [deriv_Q_eq hh0, mul_right_comm]
    exact (mul_le_mul_of_nonneg_left hlog1 hQy0).trans
      (by nlinarith only [hQy])
  have hQ'' : -(9 / 100 : ℝ) ≤ deriv (deriv Q) h * y := by
    rw [second_deriv_Q_eq hh0, mul_right_comm]
    have hm := mul_le_mul_of_nonneg_left hlog2 hQy0
    nlinarith only [hm, hQy]
  have hR := gain_R_bounds hh
  have hR'' := second_deriv_R_nonpos hh0
  have hw' : deriv (fun H ↦ U H - 1 + R H - Q H * y) h = deriv U h + RSlope h - deriv Q h * y := by
    exact (((hU.smooth.differentiableAt (by norm_num)).hasDerivAt.sub_const 1).add
      (hasDerivAt_R hh0) |>.sub (((contDiff_Q (n := 1)).differentiable (by norm_num) h).hasDerivAt.mul_const y)).deriv
  have hw'' : deriv (deriv (fun H ↦ U H - 1 + R H - Q H * y)) h =
      deriv (deriv U) h + deriv (deriv R) h - deriv (deriv Q) h * y := by
    rw [second_deriv_sub ((hU.smooth.sub contDiffAt_const).add contDiff_R.contDiffAt)
      (contDiff_Q.contDiffAt.mul contDiffAt_const),
      second_deriv_add (hU.smooth.sub contDiffAt_const) contDiff_R.contDiffAt,
      second_deriv_sub hU.smooth contDiffAt_const,
      second_deriv_mul contDiff_Q.contDiffAt contDiffAt_const]
    simp
  dsimp only
  rw [hw', hw'']
  exact ⟨by linarith [hR.1], by linarith [hR.2.1], by linarith⟩

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

lemma gain_upper_support {h : ℝ} (hh : h ∈ Ioo (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    ∃ F : ℝ → ℝ, UpperSupport gain F h ∧ deriv (deriv F) h ≤ 2 / 5 := by
  have hcc : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ) := ⟨hh.1.le, hh.2.le⟩
  obtain ⟨hp, hq, hc⟩ := gain_parameters_pos hcc
  obtain ⟨C, hC, hC'lo, hC'hi, _, hC''hi⟩ := C₀_upper_support hcc
  let r := critical ell (C₀ h) (P h) (Q h)
  let y := (P h - r) / Q h
  obtain ⟨hr0, hrP, _⟩ := critical_spec (by norm_num [ell] : 0 < ell) hc hp hq.ne'
  change 0 < r at hr0
  change r < P h at hrP
  have hy : 0 ≤ y := div_nonneg (by linarith) hq.le
  have hval : gain h = min (C₀ h * dm ^ 3) (ell * y ^ 2 + C₀ h * r ^ 3) := gain_formula hcc
  by_cases hcap : C₀ h * dm ^ 3 ≤ ell * y ^ 2 + C₀ h * r ^ 3
  · refine ⟨fun H ↦ C H * dm ^ 3, ⟨hC.smooth.mul contDiffAt_const, ?_, ?_⟩, ?_⟩
    · rw [hC.contact, hval, min_eq_left hcap]
    · filter_upwards [hC.above, Ioo_mem_nhds hh.1 hh.2] with H hCH hH
      rw [gain_formula ⟨hH.1.le, hH.2.le⟩]
      exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hCH (by norm_num [dm]))
    · rw [second_deriv_mul hC.smooth contDiffAt_const]
      simp only [deriv_const, mul_zero, add_zero]
      have hb := mul_le_mul_of_nonneg_right hC''hi (by norm_num [dm] : 0 ≤ dm ^ 3)
      norm_num [dm] at hb ⊢
      linarith
  · have hrmax : r ≤ dm := by
      by_contra! hn
      have hpow := pow_le_pow_left₀ (by norm_num [dm] : 0 ≤ dm) hn.le 3
      have hm := mul_le_mul_of_nonneg_left hpow hc.le
      have hl : 0 ≤ ell * y ^ 2 := mul_nonneg (by norm_num [ell]) (sq_nonneg y)
      exact hcap (by linarith)
    obtain ⟨U, hU, hU'lo, hU'hi, _, hU''hi⟩ := u_upper_support hcc
    let w := fun H ↦ U H - 1 + R H - Q H * y
    have hw : w h = r := by
      dsimp [w, y]
      rw [hU.contact]
      have heq : u h - 1 + R h = P h := rfl
      rw [heq]
      field_simp
      ring
    have hw0 : 0 < w h := by rw [hw]; exact hr0
    have hws : ContDiffAt ℝ 2 w h :=
      ((hU.smooth.sub contDiffAt_const).add contDiff_R.contDiffAt).sub
        (contDiff_Q.contDiffAt.mul contDiffAt_const)
    have hevent : ∀ᶠ H in 𝓝 h, 0 < w H := hws.continuousAt.eventually (Ioi_mem_nhds hw0)
    have hj := active_upper_argument_jets hcc hy hU hU'lo hU'hi hU''hi hw0
    change -(1 / 2 : ℝ) ≤ deriv w h ∧ deriv w h ≤ 17 / 50 ∧ deriv (deriv w) h ≤ 4 / 5 at hj
    refine ⟨fun H ↦ ell * y ^ 2 + C H * w H ^ 3,
      ⟨contDiffAt_const.add (hC.smooth.mul (hws.pow 3)), ?_, ?_⟩, ?_⟩
    · rw [hC.contact, hw, hval, min_eq_right (le_of_not_ge hcap)]
    · filter_upwards [hC.above, hU.above, hevent, Ioo_mem_nhds hh.1 hh.2]
        with H hCH hUH hwH hH
      have hCH0 := (gain_parameters_pos ⟨hH.1.le, hH.2.le⟩).2.2.le
      apply (gain_le_cappedEnergy ⟨hH.1.le, hH.2.le⟩ hy).trans
      unfold cappedEnergy
      apply add_le_add_right
      apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (le_min (by norm_num [dm]) (le_max_right _ _)) ?_ 3) hCH0).trans
      · exact mul_le_mul_of_nonneg_right hCH (pow_nonneg hwH.le 3)
      · apply (min_le_right _ _).trans
        apply max_le _ hwH.le
        change u H - 1 + R H - Q H * y ≤ U H - 1 + R H - Q H * y
        linarith
    · rw [second_deriv_add contDiffAt_const (hC.smooth.mul (hws.pow 3))]
      rw [second_deriv_mul_cube hC.smooth hws]
      simp only [deriv_const', deriv_const, zero_add]
      apply gain_cubic_jet_bound
      · rw [hC.contact]; exact hc.le
      · exact hC'lo
      · rw [hC.contact]; exact min_le_right _ _
      · exact hC'hi
      · exact hC''hi
      · rw [hw]; exact hr0.le
      · rw [hw]; exact hrmax
      · exact hj.1
      · exact hj.2.1
      · exact hj.2.2

theorem concaveOn_gain_corrected :
    ConcaveOn ℝ (Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) (fun h ↦ gain h - (1 / 5 : ℝ) * h ^ 2) := by
  convert concaveOn_sub_quadratic_of_support
    (K := (2 / 5 : ℝ)) continuousOn_gain (fun _ hh ↦ gain_upper_support hh) using 1
  norm_num

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma planar_switches : 0 < 1 / Real.pi ∧ 1 / Real.pi < 1 - 1 / Real.pi ∧ 1 - 1 / Real.pi < 1 := by
  have hp := Real.pi_pos
  have hi : 1 / Real.pi < (1 / 2 : ℝ) := (div_lt_div_iff₀ hp (by norm_num)).2 (by linarith [Real.pi_gt_three])
  have hi0 : 0 < 1 / Real.pi := by positivity
  exact ⟨hi0, by linarith, by linarith⟩

lemma le_rho_of_le_switch {k : ℝ} (hk : 0 ≤ k) (hb : k ≤ 1 - 1 / Real.pi) : k ≤ rho k := by
  have h1 : 1 ≤ Real.pi * (1 - k) := by
    have := (le_sub_iff_add_le).1 hb
    have hm := mul_le_mul_of_nonneg_left this Real.pi_pos.le
    rw [mul_add, mul_one_div_cancel Real.pi_pos.ne'] at hm
    linarith
  apply (nonneg_quadratic_sublevel (by positivity : 0 ≤ Real.pi * k ^ 2)
    (rho_spec hk).1 hk (rho_spec hk).2.2).1
  have hm := mul_le_mul_of_nonneg_right h1 (sq_nonneg k)
  nlinarith only [hm]

lemma rho_le_of_switch_le {k : ℝ} (hk : 0 ≤ k) (hb : 1 - 1 / Real.pi ≤ k) : rho k ≤ k := by
  have h1 : Real.pi * (1 - k) ≤ 1 := by
    have hh : 1 ≤ k + 1 / Real.pi := by linarith
    have hm := mul_le_mul_of_nonneg_left hh Real.pi_pos.le
    rw [mul_add, mul_one_div_cancel Real.pi_pos.ne'] at hm
    linarith
  by_contra! hn
  obtain ⟨hr, _, heq⟩ := rho_spec hk
  have hs := (sq_lt_sq₀ hk hr).2 hn
  have hm1 := mul_le_mul_of_nonneg_right h1 (sq_nonneg k)
  have hm2 := mul_le_mul_of_nonneg_left (show 1 - rho k ≤ 1 - k by linarith)
    (show 0 ≤ Real.pi * k ^ 2 by positivity)
  nlinarith only [hs, heq, hm1, hm2]

lemma minSection_quadratic {k : ℝ} (hk : 0 ≤ k) (ha : k ≤ 1 / Real.pi) :
    min (Real.pi * k ^ 2) (min k (rho k)) = Real.pi * k ^ 2 := by
  have hpk := (le_div_iff₀ Real.pi_pos).1 ha
  have hkq : Real.pi * k ^ 2 ≤ k := by nlinarith [mul_le_mul_of_nonneg_right hpk hk]
  exact min_eq_left (le_min hkq (hkq.trans (le_rho_of_le_switch hk (ha.trans planar_switches.2.1.le))))

lemma minSection_linear {k : ℝ} (ha : 1 / Real.pi ≤ k) (hb : k ≤ 1 - 1 / Real.pi) :
    min (Real.pi * k ^ 2) (min k (rho k)) = k := by
  have hk : 0 ≤ k := planar_switches.1.le.trans ha
  have hpk := (div_le_iff₀ Real.pi_pos).1 ha
  have hkq : k ≤ Real.pi * k ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hpk hk]
  rw [min_eq_left (le_rho_of_le_switch hk hb), min_eq_right hkq]

lemma minSection_rho {k : ℝ} (hb : 1 - 1 / Real.pi ≤ k) :
    min (Real.pi * k ^ 2) (min k (rho k)) = rho k := by
  have ha := planar_switches.2.1.le.trans hb
  have hk : 0 ≤ k := planar_switches.1.le.trans ha
  have hpk := (div_le_iff₀ Real.pi_pos).1 ha
  have hkq : k ≤ Real.pi * k ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hpk hk]
  have hrk := rho_le_of_switch_le hk hb
  rw [min_eq_right hrk, min_eq_right (hrk.trans hkq)]

def beta (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)
def J₀ (x : ℝ) : ℝ := 1 - rawWeight x
def J₁ (x : ℝ) : ℝ := (51 / 100 : ℝ) * Real.arcsin x - (49 / 100 : ℝ) * x * beta x - x / (50 * beta x)
def J₂ (x : ℝ) : ℝ := (49 / 50 : ℝ) * (2 / 3 - beta x + beta x ^ 3 / 3) -
  (x ^ 2 / beta x - 2 + 2 * beta x) / 50

lemma beta_pos {x : ℝ} (hx : x ∈ Ioo (-1) 1) : 0 < beta x := by
  apply Real.sqrt_pos.2
  nlinarith [hx.1, hx.2]

lemma beta_sq {x : ℝ} (hx : x ∈ Icc (-1) 1) : beta x ^ 2 = 1 - x ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [hx.1, hx.2]

lemma hasDerivAt_beta {x : ℝ} (hx : x ∈ Ioo (-1) 1) : HasDerivAt beta (-x / beta x) x := by
  have hsq : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  convert ((Real.hasDerivAt_sqrt hsq.ne').comp x (((hasDerivAt_id x).pow 2).const_sub 1)) using 1 <;> try rfl
  dsimp [beta]
  ring

lemma hasDerivAt_J₀ {x : ℝ} (hx : x ∈ Ioo 0 1) : HasDerivAt J₀ (density x) x := by
  convert (hasDerivAt_rawWeight hx).const_sub 1 using 1 <;> try rfl
  dsimp [density]
  ring

lemma hasDerivAt_J₁ {x : ℝ} (hx : x ∈ Ioo 0 1) : HasDerivAt J₁ (x * density x) x := by
  have hx' : x ∈ Ioo (-1) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hb := beta_sq ⟨hx'.1.le, hx'.2.le⟩
  have hb0 := beta_pos hx'
  have hd := (((Real.hasDerivAt_arcsin (by linarith [hx.1]) hx.2.ne).const_mul (51 / 100)).sub
    (((hasDerivAt_id x).const_mul (49 / 100)).mul (hasDerivAt_beta hx'))).sub
      ((hasDerivAt_id x).div ((hasDerivAt_beta hx').const_mul 50) (by positivity))
  convert hd using 1 <;> try rfl
  change x * (x * (48 - 49 * x ^ 2) / (50 * beta x ^ 3)) = _
  have hbX := congrArg (fun z ↦ x ^ 2 * z) hb
  have hbB := congrArg (fun z ↦ beta x ^ 2 * z) hb
  change _ = (51 / 100 : ℝ) * (1 / beta x) -
    ((49 / 100 : ℝ) * 1 * beta x + (49 / 100 : ℝ) * x * (-x / beta x)) -
      (1 * (50 * beta x) - x * (50 * (-x / beta x))) / (50 * beta x) ^ 2
  field_simp
  nlinarith only [hb, hbX, hbB]

lemma hasDerivAt_J₂ {x : ℝ} (hx : x ∈ Ioo 0 1) : HasDerivAt J₂ (x ^ 2 * density x) x := by
  have hx' : x ∈ Ioo (-1) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hb := beta_sq ⟨hx'.1.le, hx'.2.le⟩
  have hb0 := beta_pos hx'
  have hbd := hasDerivAt_beta hx'
  have hd := (((hbd.const_sub (2 / 3)).add ((hbd.pow 3).div_const 3)).const_mul (49 / 50)).sub
    (((((hasDerivAt_id x).pow 2).div hbd hb0.ne').sub_const 2).add (hbd.const_mul 2) |>.div_const 50)
  convert hd using 1 <;> try rfl
  change x ^ 2 * (x * (48 - 49 * x ^ 2) / (50 * beta x ^ 3)) = _
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, Pi.pow_apply] at *
  change _ = (49 / 50 : ℝ) * (-(-x / beta x) + (3 * beta x ^ 2 * (-x / beta x)) / 3) -
    ((2 * x * 1 * beta x - x ^ 2 * (-x / beta x)) / beta x ^ 2 + 2 * (-x / beta x)) / 50
  have hbX := congrArg (fun z ↦ x ^ 3 * z) hb
  have hbB := congrArg (fun z ↦ x * beta x ^ 2 * z) hb
  field_simp
  nlinarith only [hbX, hbB]

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma continuous_beta : Continuous beta := by unfold beta; fun_prop

lemma beta_ne_zero_on {x : ℝ} (hx : x ∈ Icc 0 cutoff) : beta x ≠ 0 :=
  (beta_pos ⟨by linarith [hx.1], hx.2.trans_lt cutoff_lt_one⟩).ne'

lemma continuousOn_J₀ : ContinuousOn J₀ (Icc 0 cutoff) :=
  continuousOn_const.sub continuousOn_rawWeight

lemma continuousOn_J₁ : ContinuousOn J₁ (Icc 0 cutoff) := by
  unfold J₁
  apply ContinuousOn.sub
  · exact (continuousOn_const.mul Real.continuous_arcsin.continuousOn).sub
      ((continuousOn_const.mul continuousOn_id).mul continuous_beta.continuousOn)
  · exact continuousOn_id.div (continuousOn_const.mul continuous_beta.continuousOn)
      (fun x hx ↦ mul_ne_zero (by norm_num) (beta_ne_zero_on hx))

lemma continuousOn_J₂ : ContinuousOn J₂ (Icc 0 cutoff) := by
  unfold J₂
  apply ContinuousOn.sub
  · exact continuousOn_const.mul ((continuousOn_const.sub continuous_beta.continuousOn).add
      ((continuous_beta.pow 3).continuousOn.div_const 3))
  · apply ContinuousOn.div_const
    apply ContinuousOn.add
    · exact ((continuousOn_id.pow 2).div continuous_beta.continuousOn
        (fun _ hx ↦ beta_ne_zero_on hx)).sub continuousOn_const
    · exact continuousOn_const.mul continuous_beta.continuousOn

lemma moment_integral {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ cutoff) :
    (∫ x in a..b, density x) = J₀ b - J₀ a ∧
    (∫ x in a..b, x * density x) = J₁ b - J₁ a ∧
    (∫ x in a..b, x ^ 2 * density x) = J₂ b - J₂ a := by
  have hsub : Icc a b ⊆ Icc 0 cutoff := Icc_subset_Icc ha hb
  have hd : ContinuousOn density (Icc a b) := continuousOn_density.mono hsub
  have hx {x : ℝ} (hx : x ∈ Ioo a b) : x ∈ Ioo 0 1 :=
    ⟨ha.trans_lt hx.1, hx.2.trans_le hb |>.trans cutoff_lt_one⟩
  refine ⟨intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (continuousOn_J₀.mono hsub) (fun _ hh ↦ hasDerivAt_J₀ (hx hh))
    (hd.intervalIntegrable_of_Icc hab), ?_, ?_⟩
  · exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      (continuousOn_J₁.mono hsub) (fun _ hh ↦ hasDerivAt_J₁ (hx hh))
      ((continuousOn_id.mul hd).intervalIntegrable_of_Icc hab)
  · exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      (continuousOn_J₂.mono hsub) (fun _ hh ↦ hasDerivAt_J₂ (hx hh))
      (((continuousOn_id.pow 2).mul hd).intervalIntegrable_of_Icc hab)

lemma moments_zero : J₀ 0 = 0 ∧ J₁ 0 = 0 ∧ J₂ 0 = 0 := by
  norm_num [J₀, J₁, J₂, rawWeight, beta]

def rhoChord (h a b x : ℝ) : ℝ :=
  ((b - x) * rho (a / h) + (x - a) * rho (b / h)) / (b - a)

def chordMoment (h a b : ℝ) : ℝ :=
  ((b * rho (a / h) - a * rho (b / h)) * (J₀ b - J₀ a) +
    (rho (b / h) - rho (a / h)) * (J₁ b - J₁ a)) / (b - a)

lemma rhoChord_le {h a b x : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (hab : a < b)
    (hx : x ∈ Icc a b) : rhoChord h a b x ≤ rho (x / h) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hη : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by field_simp; ring
  have hc := concaveOn_rho.2 (show a / h ∈ Ici 0 from div_nonneg ha hh.le)
    (show b / h ∈ Ici 0 from div_nonneg (ha.trans hab.le) hh.le)
    (div_nonneg (sub_nonneg.2 hx.2) hba.le) (div_nonneg (sub_nonneg.2 hx.1) hba.le) hη
  simp only [smul_eq_mul] at hc
  have ht : (b - x) / (b - a) * (a / h) + (x - a) / (b - a) * (b / h) = x / h := by
    field_simp
    ring
  rw [ht] at hc
  have heq : rhoChord h a b x = (b - x) / (b - a) * rho (a / h) +
      (x - a) / (b - a) * rho (b / h) := by unfold rhoChord; ring
  rw [heq]
  exact hc

lemma integral_rhoChord {h a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ cutoff) :
    (∫ x in a..b, density x * rhoChord h a b x) = chordMoment h a b := by
  obtain ⟨h₀, h₁, _⟩ := moment_integral ha hab hb
  have hd := continuousOn_density.mono (Icc_subset_Icc ha hb)
  have hdi : IntervalIntegrable density volume a b := hd.intervalIntegrable_of_Icc hab
  have hxi : IntervalIntegrable (fun x ↦ x * density x) volume a b :=
    (continuousOn_id.mul hd).intervalIntegrable_of_Icc hab
  have heq : (fun x ↦ density x * rhoChord h a b x) =
      (fun x ↦ ((b * rho (a / h) - a * rho (b / h)) * density x +
        (rho (b / h) - rho (a / h)) * (x * density x)) / (b - a)) := by
    funext x
    unfold rhoChord
    ring
  rw [heq, intervalIntegral.integral_div, intervalIntegral.integral_add
    (hdi.const_mul _) (hxi.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, h₀, h₁]
  rfl

lemma section_density_integrable (h : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ cutoff) :
    IntervalIntegrable (fun x ↦ density x * sectionLength x h) volume a b :=
  ((continuousOn_density.mono (Icc_subset_Icc ha hb)).mul
    (continuous_sectionLength_X h).continuousOn).intervalIntegrable_of_Icc hab

lemma integral_section_quadratic {h : ℝ} (hh : 0 < h) (hx : h / Real.pi ≤ cutoff) :
    (∫ x in (0 : ℝ)..h / Real.pi, density x * sectionLength x h) =
      Real.pi / h ^ 2 * J₂ (h / Real.pi) := by
  have hx0 : 0 ≤ h / Real.pi := div_nonneg hh.le Real.pi_pos.le
  have hi := (moment_integral (a := 0) le_rfl hx0 hx).2.2
  rw [moments_zero.2.2, sub_zero] at hi
  calc
    _ = ∫ x in (0 : ℝ)..h / Real.pi, (Real.pi / h ^ 2) * (x ^ 2 * density x) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hx0]
      intro x hxx
      have hq : x / h ≤ 1 / Real.pi := by
        apply (div_le_div_iff₀ hh Real.pi_pos).2
        have := (le_div_iff₀ Real.pi_pos).1 hxx.2
        linarith
      change density x * sectionLength x h = _
      rw [sectionLength, minSection_quadratic (div_nonneg hxx.1 hh.le) hq]
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul, hi]

lemma integral_section_linear {h y : ℝ} (hh : 0 < h)
    (hxy : h / Real.pi ≤ y) (hy : y ≤ cutoff) (hys : y ≤ h * (1 - 1 / Real.pi)) :
    (∫ x in h / Real.pi..y, density x * sectionLength x h) =
      (J₁ y - J₁ (h / Real.pi)) / h := by
  have hx0 : 0 ≤ h / Real.pi := div_nonneg hh.le Real.pi_pos.le
  have hi := (moment_integral hx0 hxy hy).2.1
  calc
    _ = ∫ x in h / Real.pi..y, (x * density x) / h := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hxy]
      intro x hxx
      have ha : 1 / Real.pi ≤ x / h := by
        apply (div_le_div_iff₀ Real.pi_pos hh).2
        have := (div_le_iff₀ Real.pi_pos).1 hxx.1
        linarith
      have hb : x / h ≤ 1 - 1 / Real.pi := (div_le_iff₀ hh).2 (by nlinarith [hxx.2])
      change density x * sectionLength x h = _
      rw [sectionLength, minSection_linear ha hb]
      ring
    _ = _ := by rw [intervalIntegral.integral_div, hi]

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma integral_section_chord {h a b : ℝ} (hh : 0 < h) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ cutoff) (hsa : h * (1 - 1 / Real.pi) ≤ a) :
    chordMoment h a b ≤ ∫ x in a..b, density x * sectionLength x h := by
  rw [← integral_rhoChord ha hab hb]
  rcases hab.eq_or_lt with rfl | hab'
  · simp
  have hd := continuousOn_density.mono (Icc_subset_Icc ha hb)
  have hch : Continuous (fun x ↦ rhoChord h a b x) := by unfold rhoChord; fun_prop
  apply intervalIntegral.integral_mono_on hab
    ((hd.mul hch.continuousOn).intervalIntegrable_of_Icc hab)
    (section_density_integrable h ha hab hb)
  intro x hx
  have hxs : 1 - 1 / Real.pi ≤ x / h := (le_div_iff₀ hh).2 (by nlinarith [hx.1])
  rw [sectionLength, minSection_rho hxs]
  exact mul_le_mul_of_nonneg_left (rhoChord_le hh ha hab' hx) (density_nonneg ⟨ha.trans hx.1, hx.2.trans hb⟩)

def twoChordBaseline (h : ℝ) : ℝ :=
  let x := h / Real.pi
  let y := h * (1 - 1 / Real.pi)
  let z := (y + cutoff) / 2
  lambda * h / Real.pi + ell * t h - 1 + Real.pi / h ^ 2 * J₂ x +
    (J₁ y - J₁ x) / h + chordMoment h y z + chordMoment h z cutoff

def linearBaseline (h : ℝ) : ℝ :=
  lambda * h / Real.pi + ell * t h - 1 + Real.pi / h ^ 2 * J₂ (h / Real.pi) +
    (J₁ cutoff - J₁ (h / Real.pi)) / h

lemma twoChordBaseline_le {h : ℝ} (hh : 0 < h)
    (hy : h * (1 - 1 / Real.pi) ≤ cutoff) : twoChordBaseline h ≤ baseline h := by
  let x := h / Real.pi
  let y := h * (1 - 1 / Real.pi)
  let z := (y + cutoff) / 2
  let F := fun X ↦ density X * sectionLength X h
  have hx0 : 0 ≤ x := div_nonneg hh.le Real.pi_pos.le
  have hxy : x ≤ y := by
    have hm := mul_le_mul_of_nonneg_left planar_switches.2.1.le hh.le
    simpa only [mul_one_div] using hm
  have hyz : y ≤ z := by dsimp [z]; linarith
  have hzD : z ≤ cutoff := by dsimp [z]; linarith
  have h0y : 0 ≤ y := hx0.trans hxy
  have h0z : 0 ≤ z := h0y.trans hyz
  have h0xI := section_density_integrable h (a := 0) le_rfl hx0 (hxy.trans hy)
  have hxyI := section_density_integrable h hx0 hxy hy
  have hyzI := section_density_integrable h h0y hyz hzD
  have hzDI := section_density_integrable h h0z hzD le_rfl
  have hi1 := intervalIntegral.integral_add_adjacent_intervals h0xI hxyI
  have hi2 := intervalIntegral.integral_add_adjacent_intervals (h0xI.trans hxyI) hyzI
  have hi3 := intervalIntegral.integral_add_adjacent_intervals ((h0xI.trans hxyI).trans hyzI) hzDI
  have hq := integral_section_quadratic hh (hxy.trans hy)
  have hl := integral_section_linear hh hxy hy (show y ≤ h * (1 - 1 / Real.pi) from le_rfl)
  have hc1 := integral_section_chord hh h0y hyz hzD (show h * (1 - 1 / Real.pi) ≤ y from le_rfl)
  have hc2 := integral_section_chord hh h0z hzD le_rfl (show h * (1 - 1 / Real.pi) ≤ z from hyz)
  have heq := baseline_layer_cake hh
  change baseline h + 1 = lambda * h / Real.pi + ell * t h + ∫ X in (0 : ℝ)..cutoff, F X at heq
  change (∫ X in (0 : ℝ)..x, F X) + (∫ X in x..y, F X) = ∫ X in (0 : ℝ)..y, F X at hi1
  change (∫ X in (0 : ℝ)..y, F X) + (∫ X in y..z, F X) = ∫ X in (0 : ℝ)..z, F X at hi2
  change (∫ X in (0 : ℝ)..z, F X) + (∫ X in z..cutoff, F X) = ∫ X in (0 : ℝ)..cutoff, F X at hi3
  change (∫ X in (0 : ℝ)..x, F X) = Real.pi / h ^ 2 * J₂ x at hq
  change (∫ X in x..y, F X) = (J₁ y - J₁ x) / h at hl
  change chordMoment h y z ≤ ∫ X in y..z, F X at hc1
  change chordMoment h z cutoff ≤ ∫ X in z..cutoff, F X at hc2
  change lambda * h / Real.pi + ell * t h - 1 + Real.pi / h ^ 2 * J₂ x +
    (J₁ y - J₁ x) / h + chordMoment h y z + chordMoment h z cutoff ≤ baseline h
  linarith

lemma linearBaseline_eq {h : ℝ} (hh : 0 < h) (hx : h / Real.pi ≤ cutoff)
    (hy : cutoff ≤ h * (1 - 1 / Real.pi)) : linearBaseline h = baseline h := by
  have hx0 : 0 ≤ h / Real.pi := div_nonneg hh.le Real.pi_pos.le
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (section_density_integrable h le_rfl hx0 hx) (section_density_integrable h hx0 hx le_rfl)
  have hq := integral_section_quadratic hh hx
  have hl := integral_section_linear hh hx le_rfl hy
  have heq := baseline_layer_cake hh
  change baseline h + 1 = lambda * h / Real.pi + ell * t h +
    ∫ X in (0 : ℝ)..cutoff, density X * sectionLength X h at heq
  unfold linearBaseline
  linarith

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma semiconcave_chord_bound {f : ℝ → ℝ} {a b c x : ℝ} (hab : a < b) (hc : 0 ≤ c)
    (hf : ConcaveOn ℝ (Icc a b) (fun y ↦ f y - c * y ^ 2)) (hx : x ∈ Icc a b) :
    min (f a) (f b) - c * (b - a) ^ 2 / 4 ≤ f x := by
  let w := (b - x) / (b - a)
  let v := (x - a) / (b - a)
  have hd : 0 < b - a := sub_pos.2 hab
  have hw : 0 ≤ w := div_nonneg (sub_nonneg.2 hx.2) hd.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.2 hx.1) hd.le
  have hsum : w + v = 1 := by dsimp [w, v]; field_simp; ring
  have harg : w * a + v * b = x := by dsimp [w, v]; field_simp; ring
  have hcon := hf.2 (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hw hv hsum
  simp only [smul_eq_mul, harg] at hcon
  have hmin : min (f a) (f b) ≤ w * f a + v * f b := by
    have ha := mul_le_mul_of_nonneg_left (min_le_left (f a) (f b)) hw
    have hb := mul_le_mul_of_nonneg_left (min_le_right (f a) (f b)) hv
    calc
      _ = w * min (f a) (f b) + v * min (f a) (f b) := by rw [← add_mul, hsum, one_mul]
      _ ≤ _ := add_le_add ha hb
  have hcorr : w * c * a ^ 2 + v * c * b ^ 2 - c * x ^ 2 = c * (x - a) * (b - x) := by
    dsimp [w, v]
    field_simp
    ring
  have hprod : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * x - a - b)]
  have hprod' := mul_le_mul_of_nonneg_left hprod hc
  nlinarith only [hcon, hmin, hcorr, hprod']

lemma baseline_chord_lower {a b x l r : ℝ} (ha : 0 < a) (hab : a < b)
    (hx : x ∈ Icc a b) (hl : l ≤ baseline a) (hr : r ≤ baseline b) :
    min l r - (b - a) ^ 2 / (4 * a ^ 2) ≤ baseline x := by
  have hf : ConcaveOn ℝ (Icc a b) (fun y ↦ baseline y - (1 / a ^ 2) * y ^ 2) := by
    convert concaveOn_baseline_corrected (b := b) ha using 1
    funext y
    ring
  have hbound := semiconcave_chord_bound hab (by positivity : 0 ≤ (1 : ℝ) / a ^ 2) hf hx
  have hmin := min_le_min hl hr
  have heq : (b - a) ^ 2 / (4 * a ^ 2) = (1 / a ^ 2) * (b - a) ^ 2 / 4 := by ring
  rw [heq]
  linarith

lemma combined_chord_lower {a b x l r : ℝ} (ha : (51 / 50 : ℝ) ≤ a)
    (hb : b ≤ (81 / 50 : ℝ)) (hab : a < b) (hx : x ∈ Icc a b)
    (hl : l ≤ baseline a + gain a) (hr : r ≤ baseline b + gain b) :
    min l r - (1 / a ^ 2 + (1 / 5 : ℝ)) * (b - a) ^ 2 / 4 ≤ baseline x + gain x := by
  have ha0 : 0 < a := by linarith
  have hg := concaveOn_gain_corrected.subset (Icc_subset_Icc ha hb) (convex_Icc a b)
  have hf : ConcaveOn ℝ (Icc a b)
      (fun y ↦ baseline y + gain y - (1 / a ^ 2 + (1 / 5 : ℝ)) * y ^ 2) := by
    apply ((concaveOn_baseline_corrected (b := b) ha0).add hg).congr
    intro y _
    dsimp
    ring
  have hbound := semiconcave_chord_bound hab (by positivity : 0 ≤ (1 : ℝ) / a ^ 2 + 1 / 5) hf hx
  have hmin := min_le_min hl hr
  linarith

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma coarse_switch_bounds : (17 / 25 : ℝ) ≤ 1 - 1 / Real.pi ∧
    1 - 1 / Real.pi ≤ 15 / 22 := by
  constructor
  · have hp : (25 / 8 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
    have hi : 1 / Real.pi ≤ (8 / 25 : ℝ) := (div_le_iff₀ Real.pi_pos).2 (by linarith)
    linarith
  · have hp : Real.pi ≤ (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
    have hi : (7 / 22 : ℝ) ≤ 1 / Real.pi := (le_div_iff₀ Real.pi_pos).2 (by linarith)
    linarith

lemma coarse_cutoff_bounds : (49 / 50 : ℝ) ≤ cutoff ∧ cutoff ≤ 99 / 100 := by
  constructor <;> nlinarith [cutoff_pos, cutoff_sq]

lemma twoChordBaseline_le_of_range {h : ℝ} (hh : 0 < h) (hu : h ≤ 71 / 50) :
    twoChordBaseline h ≤ baseline h := by
  apply twoChordBaseline_le hh
  have he := mul_le_mul_of_nonneg_left coarse_switch_bounds.2 hh.le
  nlinarith [coarse_cutoff_bounds.1]

lemma linearBaseline_eq_of_range {h : ℝ} (hl : (73 / 50 : ℝ) ≤ h) (hu : h ≤ 9 / 4) :
    linearBaseline h = baseline h := by
  have hh : 0 < h := by linarith
  apply linearBaseline_eq hh
  · apply (div_le_iff₀ Real.pi_pos).2
    have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    nlinarith [coarse_cutoff_bounds.1,
      mul_nonneg (sub_nonneg.2 hpi) (sub_nonneg.2 coarse_cutoff_bounds.1)]
  · have he := mul_le_mul_of_nonneg_left coarse_switch_bounds.1 hh.le
    nlinarith [coarse_cutoff_bounds.2]

end CubicTorus.Scalar

namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

def e0 : ℝ := Real.pi
lemma b0 : Encl e0 (314159265358979 / 100000000000000 : ℝ) (15707963267949 / 5000000000000 : ℝ) := by
  change Encl Real.pi _ _
  constructor
  · have := Real.pi_gt_d20; norm_num at this ⊢; linarith
  · have := Real.pi_lt_d20; norm_num at this ⊢; linarith

def e1 : ℝ := (48 : ℝ)
lemma b1 : Encl e1 (48 : ℝ) (48 : ℝ) := by
  exact Encl.exact (48 : ℝ)

def e2 : ℝ := Real.sqrt e1
lemma b2 : Encl e2 (277128129211 / 40000000000 : ℝ) (1732050807569 / 250000000000 : ℝ) := by
  exact Encl.sqrt b1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e3 : ℝ := (7 : ℝ)
lemma b3 : Encl e3 (7 : ℝ) (7 : ℝ) := by
  exact Encl.exact (7 : ℝ)

def e4 : ℝ := e2 / e3
lemma b4 : Encl e4 (98974331861 / 100000000000 : ℝ) (989743318611 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2 b3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e5 : ℝ := (1 : ℝ)
lemma b5 : Encl e5 (1 : ℝ) (1 : ℝ) := by
  exact Encl.exact (1 : ℝ)

def e6 : ℝ := e5 / e0
lemma b6 : Encl e6 (318309886183 / 1000000000000 : ℝ) (39788735773 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b5 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e7 : ℝ := e5 - e6
lemma b7 : Encl e7 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b6 (by norm_num) (by norm_num)

def e8 : ℝ := (49 / 50 : ℝ)
lemma b8 : Encl e8 (49 / 50 : ℝ) (49 / 50 : ℝ) := by
  exact Encl.exact (49 / 50 : ℝ)

def e9 : ℝ := (7 / 25 : ℝ)
lemma b9 : Encl e9 (7 / 25 : ℝ) (7 / 25 : ℝ) := by
  exact Encl.exact (7 / 25 : ℝ)

def e10 : ℝ := (21 / 100 : ℝ)
lemma b10 : Encl e10 (21 / 100 : ℝ) (21 / 100 : ℝ) := by
  exact Encl.exact (21 / 100 : ℝ)

def e11 : ℝ := (16 / 25 : ℝ)
lemma b11 : Encl e11 (16 / 25 : ℝ) (16 / 25 : ℝ) := by
  exact Encl.exact (16 / 25 : ℝ)

def e12 : ℝ := e11 / e0
lemma b12 : Encl e12 (203718327157 / 1000000000000 : ℝ) (101859163579 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b11 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e13 : ℝ := e11 * e7
lemma b13 : Encl e13 (218140836421 / 500000000000 : ℝ) (436281672843 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b11 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e14 : ℝ := e8 * e11
lemma b14 : Encl e14 (392 / 625 : ℝ) (392 / 625 : ℝ) := by
  exact Encl.mul_nonneg b8 b11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e15 : ℝ := e14 / e0
lemma b15 : Encl e15 (99821980307 / 500000000000 : ℝ) (39928792123 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b14 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e16 : ℝ := e11 ^ 2
lemma b16 : Encl e16 (256 / 625 : ℝ) (256 / 625 : ℝ) := by
  exact Encl.pow b11 (by norm_num) 2 (by norm_num) (by norm_num)

def e17 : ℝ := (4 : ℝ)
lemma b17 : Encl e17 (4 : ℝ) (4 : ℝ) := by
  exact Encl.exact (4 : ℝ)

def e18 : ℝ := e17 * e16
lemma b18 : Encl e18 (1024 / 625 : ℝ) (1024 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e19 : ℝ := e18 / e0
lemma b19 : Encl e19 (521518917523 / 1000000000000 : ℝ) (130379729381 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b18 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e20 : ℝ := e5 + e19
lemma b20 : Encl e20 (1521518917523 / 1000000000000 : ℝ) (380379729381 / 250000000000 : ℝ) := by
  exact Encl.add b5 b19 (by norm_num) (by norm_num)

def e21 : ℝ := Real.sqrt e20
lemma b21 : Encl e21 (1233498649177 / 1000000000000 : ℝ) (1233498649179 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e22 : ℝ := e5 + e21
lemma b22 : Encl e22 (2233498649177 / 1000000000000 : ℝ) (2233498649179 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b21 (by norm_num) (by norm_num)

def e23 : ℝ := (2 : ℝ)
lemma b23 : Encl e23 (2 : ℝ) (2 : ℝ) := by
  exact Encl.exact (2 : ℝ)

def e24 : ℝ := e23 / e22
lemma b24 : Encl e24 (895456104589 / 1000000000000 : ℝ) (895456104591 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e25 : ℝ := e9 * e24
lemma b25 : Encl e25 (62681927321 / 250000000000 : ℝ) (125363854643 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e26 : ℝ := e15 + e25
lemma b26 : Encl e26 (225185834949 / 500000000000 : ℝ) (450371669901 / 1000000000000 : ℝ) := by
  exact Encl.add b15 b25 (by norm_num) (by norm_num)

def e27 : ℝ := e26 - e5
lemma b27 : Encl e27 (-274814165051 / 500000000000 : ℝ) (-549628330099 / 1000000000000 : ℝ) := by
  exact Encl.sub b26 b5 (by norm_num) (by norm_num)

def e28 : ℝ := e0 / e16
lemma b28 : Encl e28 (1917475984857 / 250000000000 : ℝ) (7669903939429 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e29 : ℝ := (2 / 3 : ℝ)
lemma b29 : Encl e29 (2 / 3 : ℝ) (2 / 3 : ℝ) := by
  exact Encl.exact (2 / 3 : ℝ)

def e30 : ℝ := e12 ^ 2
lemma b30 : Encl e30 (41501156819 / 1000000000000 : ℝ) (41501156821 / 1000000000000 : ℝ) := by
  exact Encl.pow b12 (by norm_num) 2 (by norm_num) (by norm_num)

def e31 : ℝ := e5 - e30
lemma b31 : Encl e31 (958498843179 / 1000000000000 : ℝ) (958498843181 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b30 (by norm_num) (by norm_num)

def e32 : ℝ := Real.sqrt e31
lemma b32 : Encl e32 (39161181661 / 40000000000 : ℝ) (979029541527 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e33 : ℝ := e29 - e32
lemma b33 : Encl e33 (-312362874861 / 1000000000000 : ℝ) (-156181437429 / 500000000000 : ℝ) := by
  exact Encl.sub b29 b32 (by norm_num) (by norm_num)

def e34 : ℝ := e32 ^ 3
lemma b34 : Encl e34 (938398682989 / 1000000000000 : ℝ) (234599670749 / 250000000000 : ℝ) := by
  exact Encl.pow b32 (by norm_num) 3 (by norm_num) (by norm_num)

def e35 : ℝ := (3 : ℝ)
lemma b35 : Encl e35 (3 : ℝ) (3 : ℝ) := by
  exact Encl.exact (3 : ℝ)

def e36 : ℝ := e34 / e35
lemma b36 : Encl e36 (78199890249 / 250000000000 : ℝ) (312799560999 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b34 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e37 : ℝ := e33 + e36
lemma b37 : Encl e37 (87337227 / 200000000000 : ℝ) (436686141 / 1000000000000 : ℝ) := by
  exact Encl.add b33 b36 (by norm_num) (by norm_num)

def e38 : ℝ := e8 * e37
lemma b38 : Encl e38 (106988103 / 250000000000 : ℝ) (427952419 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e39 : ℝ := e30 / e32
lemma b39 : Encl e39 (21195048289 / 500000000000 : ℝ) (21195048291 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b30 b32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e40 : ℝ := e39 - e23
lemma b40 : Encl e40 (-978804951711 / 500000000000 : ℝ) (-978804951709 / 500000000000 : ℝ) := by
  exact Encl.sub b39 b23 (by norm_num) (by norm_num)

def e41 : ℝ := e23 * e32
lemma b41 : Encl e41 (39161181661 / 20000000000 : ℝ) (979029541527 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e42 : ℝ := e40 + e41
lemma b42 : Encl e42 (112294907 / 250000000000 : ℝ) (112294909 / 250000000000 : ℝ) := by
  exact Encl.add b40 b41 (by norm_num) (by norm_num)

def e43 : ℝ := (50 : ℝ)
lemma b43 : Encl e43 (50 : ℝ) (50 : ℝ) := by
  exact Encl.exact (50 : ℝ)

def e44 : ℝ := e42 / e43
lemma b44 : Encl e44 (1122949 / 125000000000 : ℝ) (8983593 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b42 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e45 : ℝ := e38 - e44
lemma b45 : Encl e45 (418968819 / 1000000000000 : ℝ) (418968827 / 1000000000000 : ℝ) := by
  exact Encl.sub b38 b44 (by norm_num) (by norm_num)

def e46 : ℝ := e28 * e45
lemma b46 : Encl e46 (642690119 / 200000000000 : ℝ) (3213450657 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b28 b45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e47 : ℝ := e27 + e46
lemma b47 : Encl e47 (-546414879507 / 1000000000000 : ℝ) (-273207439721 / 500000000000 : ℝ) := by
  exact Encl.add b27 b46 (by norm_num) (by norm_num)

def e48 : ℝ := e13 ^ 2
lemma b48 : Encl e48 (190341698057 / 1000000000000 : ℝ) (190341698059 / 1000000000000 : ℝ) := by
  exact Encl.pow b13 (by norm_num) 2 (by norm_num) (by norm_num)

def e49 : ℝ := e5 - e48
lemma b49 : Encl e49 (809658301941 / 1000000000000 : ℝ) (809658301943 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b48 (by norm_num) (by norm_num)

def e50 : ℝ := Real.sqrt e49
lemma b50 : Encl e50 (22495253693 / 25000000000 : ℝ) (449905073861 / 500000000000 : ℝ) := by
  exact Encl.sqrt b49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e51 : ℝ := e5 + e50
lemma b51 : Encl e51 (47495253693 / 25000000000 : ℝ) (949905073861 / 500000000000 : ℝ) := by
  exact Encl.add b5 b50 (by norm_num) (by norm_num)

def e52 : ℝ := e13 / e51
lemma b52 : Encl e52 (57411219927 / 250000000000 : ℝ) (229644879709 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b13 b51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e53 : ℝ := e52 ^ 2
lemma b53 : Encl e53 (6592096347 / 125000000000 : ℝ) (52736770777 / 1000000000000 : ℝ) := by
  exact Encl.pow b52 (by norm_num) 2 (by norm_num) (by norm_num)

def e54 : ℝ := e5 + e53
lemma b54 : Encl e54 (131592096347 / 125000000000 : ℝ) (1052736770777 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b53 (by norm_num) (by norm_num)

def e55 : ℝ := Real.sqrt e54
lemma b55 : Encl e55 (12825370187 / 12500000000 : ℝ) (1026029614961 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e56 : ℝ := e5 + e55
lemma b56 : Encl e56 (25325370187 / 12500000000 : ℝ) (2026029614961 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b55 (by norm_num) (by norm_num)

def e57 : ℝ := e52 / e56
lemma b57 : Encl e57 (28336811813 / 250000000000 : ℝ) (56673623627 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b52 b56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e58 : ℝ := Real.arcsin e13
lemma b58 : Encl e58 (14108192723 / 31250000000 : ℝ) (56432770893 / 125000000000 : ℝ) := by
  apply Encl.arcsin (z := e13) (a := (28336811813 / 250000000000 : ℝ)) (b := (56673623627 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (218140836421 / 500000000000 : ℝ) by norm_num).trans b13.1
        exact b13.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e13) (28336811813 / 250000000000 : ℝ) (56673623627 / 500000000000 : ℝ) from b57) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e59 : ℝ := (51 / 100 : ℝ)
lemma b59 : Encl e59 (51 / 100 : ℝ) (51 / 100 : ℝ) := by
  exact Encl.exact (51 / 100 : ℝ)

def e60 : ℝ := e59 * e58
lemma b60 : Encl e60 (230245705239 / 1000000000000 : ℝ) (57561426311 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e61 : ℝ := (49 / 100 : ℝ)
lemma b61 : Encl e61 (49 / 100 : ℝ) (49 / 100 : ℝ) := by
  exact Encl.exact (49 / 100 : ℝ)

def e62 : ℝ := e61 * e13
lemma b62 : Encl e62 (53444504923 / 250000000000 : ℝ) (106889009847 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e63 : ℝ := e62 * e50
lemma b63 : Encl e63 (96179815739 / 500000000000 : ℝ) (192359631481 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b62 b50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e64 : ℝ := e60 - e63
lemma b64 : Encl e64 (18943036879 / 500000000000 : ℝ) (18943036883 / 500000000000 : ℝ) := by
  exact Encl.sub b60 b63 (by norm_num) (by norm_num)

def e65 : ℝ := e43 * e50
lemma b65 : Encl e65 (22495253693 / 500000000 : ℝ) (449905073861 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e66 : ℝ := e13 / e65
lemma b66 : Encl e66 (9697193879 / 1000000000000 : ℝ) (242429847 / 25000000000 : ℝ) := by
  exact Encl.div_nonneg b13 b65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e67 : ℝ := e64 - e66
lemma b67 : Encl e67 (14094439939 / 500000000000 : ℝ) (28188879887 / 1000000000000 : ℝ) := by
  exact Encl.sub b64 b66 (by norm_num) (by norm_num)

def e68 : ℝ := e5 + e32
lemma b68 : Encl e68 (79161181661 / 40000000000 : ℝ) (1979029541527 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b32 (by norm_num) (by norm_num)

def e69 : ℝ := e12 / e68
lemma b69 : Encl e69 (2573462433 / 25000000000 : ℝ) (102938497321 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b12 b68 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e70 : ℝ := e69 ^ 2
lemma b70 : Encl e70 (1059633423 / 100000000000 : ℝ) (10596334231 / 1000000000000 : ℝ) := by
  exact Encl.pow b69 (by norm_num) 2 (by norm_num) (by norm_num)

def e71 : ℝ := e5 + e70

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
