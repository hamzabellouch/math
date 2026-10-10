import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
namespace SKGap

def entropyEll (u : ℝ) : ℝ := -log (1 - u) - u

def entropySlack (B u : ℝ) : ℝ := u ^ 2 / 2 - B * entropyEll u

theorem entropyEll_hasDerivAt {u : ℝ} (hu : u < 1) :
    HasDerivAt entropyEll (u / (1 - u)) u := by
  have hd := ((((hasDerivAt_id u).const_sub 1).log (by linarith : 1 - u ≠ 0)).neg).sub
    (hasDerivAt_id u)
  convert! hd using 1
  dsimp
  field_simp [show 1 - u ≠ 0 by linarith]
  ring

theorem entropyEll_nonneg {u : ℝ} (hu : u < 1) : 0 ≤ entropyEll u := by
  have h := log_le_sub_one_of_pos (by linarith : 0 < 1 - u)
  dsimp [entropyEll]
  linarith

theorem entropyEll_le_half_sq_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    entropyEll u ≤ u ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x => x ^ 2 / 2 - entropyEll x
  have hd (x : ℝ) (hx : x < 1) : HasDerivAt f (-x ^ 2 / (1 - x)) x := by
    convert! (((hasDerivAt_id x).pow 2).div_const 2).sub (entropyEll_hasDerivAt hx) using 1
    dsimp
    field_simp [show 1 - x ≠ 0 by linarith]
    ring
  have hm : AntitoneOn f (Iic 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
    · intro x hx
      exact (hd x (by simp only [mem_Iic] at hx; linarith)).continuousAt.continuousWithinAt
    · intro x hx
      have hx0 : x < 0 := by simpa only [interior_Iic, mem_Iio] using hx
      exact (hd x (by linarith)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : x < 0 := by simpa only [interior_Iic, mem_Iio] using hx
      rw [(hd x (by linarith)).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by linarith)
  have h := hm (show u ∈ Iic 0 from hu) (show (0 : ℝ) ∈ Iic 0 by simp) hu
  simpa [f, entropyEll] using h

theorem entropySlack_pos_of_neg {B u : ℝ} (hB0 : 0 ≤ B) (hB1 : B < 1) (hu : u < 0) :
    0 < entropySlack B u := by
  have he := mul_le_mul_of_nonneg_left (entropyEll_le_half_sq_of_nonpos hu.le) hB0
  have hs : 0 < u ^ 2 := sq_pos_of_ne_zero hu.ne
  dsimp [entropySlack]
  nlinarith

theorem value_le_of_deriv_nonneg {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, 0 ≤ g x) : f a ≤ f b := by
  have hm : MonotoneOn f (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x (interior_subset hx)).deriv]
      exact hg x (interior_subset hx)
  exact hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

theorem half_sq_le_entropyEll {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    u ^ 2 / 2 ≤ entropyEll u := by
  let f : ℝ → ℝ := fun x => entropyEll x - x ^ 2 / 2
  have hd (x : ℝ) (hx : x < 1) : HasDerivAt f (x ^ 2 / (1 - x)) x := by
    convert! (entropyEll_hasDerivAt hx).sub (((hasDerivAt_id x).pow 2).div_const 2) using 1
    dsimp
    field_simp [show 1 - x ≠ 0 by linarith]
    ring
  have h := value_le_of_deriv_nonneg hu0 (fun x hx => hd x (hx.2.trans_lt hu1))
    (fun x hx => div_nonneg (sq_nonneg x) (by linarith [hx.2]))
  simpa [f, entropyEll] using h

theorem entropySlack_cubic_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    u ^ 3 / 6 ≤ entropySlack (1 - u) u := by
  let f : ℝ → ℝ := fun x => entropySlack (1 - x) x - x ^ 3 / 6
  have hd (x : ℝ) (hx : x < 1) : HasDerivAt f (entropyEll x - x ^ 2 / 2) x := by
    convert! ((((hasDerivAt_id x).pow 2).div_const 2).sub
      (((hasDerivAt_id x).const_sub 1).mul (entropyEll_hasDerivAt hx))).sub
        (((hasDerivAt_id x).pow 3).div_const 6) using 1
    dsimp
    field_simp [show 1 - x ≠ 0 by linarith]
    ring
  have h := value_le_of_deriv_nonneg hu0 (fun x hx => hd x (hx.2.trans_lt hu1))
    (fun x hx => sub_nonneg.mpr (half_sq_le_entropyEll hx.1 (hx.2.trans_lt hu1)))
  simpa [f, entropySlack, entropyEll] using h

theorem entropySlack_cubic_lower_of_le {B u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hB : B ≤ 1 - u) : u ^ 3 / 6 ≤ entropySlack B u := by
  have h := mul_le_mul_of_nonneg_right hB (entropyEll_nonneg hu1)
  have hl := entropySlack_cubic_lower hu0 hu1
  dsimp [entropySlack] at *
  linarith

theorem entropySlack_pos {B u : ℝ} (hB0 : 0 ≤ B) (hB1 : B < 1)
    (huB : u ≤ 1 - B) (hu1 : u < 1) (hu0 : u ≠ 0) : 0 < entropySlack B u := by
  rcases hu0.lt_or_gt with hneg | hpos
  · exact entropySlack_pos_of_neg hB0 hB1 hneg
  · have h := entropySlack_cubic_lower_of_le hpos.le hu1 (by linarith : B ≤ 1 - u)
    exact (div_pos (pow_pos hpos 3) (by norm_num : (0 : ℝ) < 6)).trans_le h

theorem log_one_add_cubic_upper {x : ℝ} (hx : 0 ≤ x) :
    log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  let f : ℝ → ℝ := fun y => y - y ^ 2 / 2 + y ^ 3 / 3 - log (1 + y)
  have hd (y : ℝ) (hy : 0 ≤ y) : HasDerivAt f (y ^ 3 / (1 + y)) y := by
    convert! (((hasDerivAt_id y).sub (((hasDerivAt_id y).pow 2).div_const 2)).add
      (((hasDerivAt_id y).pow 3).div_const 3)).sub
        (((hasDerivAt_id y).const_add 1).log (by linarith : 1 + y ≠ 0)) using 1
    dsimp
    field_simp [show 1 + y ≠ 0 by linarith]
    ring
  have h := value_le_of_deriv_nonneg hx (fun y hy => hd y hy.1)
    (fun y hy => div_nonneg (pow_nonneg hy.1 3) (by linarith [hy.1]))
  simpa [f] using h

def entropyVarianceSlack (k B C : ℝ) : ℝ :=
  C ^ 2 / k - 1 - log (C ^ 2 / k) - (C - B) ^ 2 / (1 + k)

def entropyVarianceSlope (k B C : ℝ) : ℝ :=
  2 * C / k - 2 / C - 2 * (C - B) / (1 + k)

theorem entropyVarianceSlack_hasDerivAt {k B C : ℝ} (hk : 0 < k) (hC : 0 < C) :
    HasDerivAt (entropyVarianceSlack k B) (entropyVarianceSlope k B C) C := by
  have hden : C ^ 2 / k ≠ 0 := div_ne_zero (pow_ne_zero 2 hC.ne') hk.ne'
  convert! (((((hasDerivAt_id C).pow 2).div_const k).sub_const 1).sub
    ((((hasDerivAt_id C).pow 2).div_const k).log hden)).sub
      ((((hasDerivAt_id C).sub_const B).pow 2).div_const (1 + k)) using 1
  dsimp [entropyVarianceSlope]
  field_simp

theorem entropyVarianceSlope_hasDerivAt {k B C : ℝ} (hk : 0 < k) (hC : 0 < C) :
    HasDerivAt (entropyVarianceSlope k B) (2 / (k * (1 + k)) + 2 / C ^ 2) C := by
  convert! ((((hasDerivAt_id C).const_mul 2).div_const k).sub
    ((hasDerivAt_const C (2 : ℝ)).div (hasDerivAt_id C) hC.ne')).sub
      ((((hasDerivAt_id C).sub_const B).const_mul 2).div_const (1 + k)) using 1
  dsimp
  field_simp
  ring

theorem entropyVariance_curvature_one {k C : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (_hC : 0 < C) :
    1 ≤ 2 / (k * (1 + k)) + 2 / C ^ 2 := by
  have hp : 0 < k * (1 + k) := mul_pos hk0 (by linarith)
  have hk2 : k * (1 + k) ≤ 2 := by nlinarith
  have hdiv : 1 ≤ 2 / (k * (1 + k)) := by rwa [le_div_iff₀ hp, one_mul]
  have hpos : 0 ≤ 2 / C ^ 2 := div_nonneg (by norm_num) (sq_nonneg _)
  linarith

theorem entropyVariance_taylor_lower {k B C₀ C : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hC₀ : 0 < C₀) (hC : C₀ ≤ C) :
    entropyVarianceSlack k B C₀ + entropyVarianceSlope k B C₀ * (C - C₀) +
      (C - C₀)^2 / 2 ≤ entropyVarianceSlack k B C := by
  have hslope (x : ℝ) (hx : C₀ ≤ x) :
      entropyVarianceSlope k B C₀ + (x - C₀) ≤ entropyVarianceSlope k B x := by
    have h := value_le_of_deriv_nonneg hx
      (f := fun y => entropyVarianceSlope k B y - y)
      (g := fun y => 2 / (k * (1 + k)) + 2 / y ^ 2 - 1)
      (fun y hy => (entropyVarianceSlope_hasDerivAt hk0 (hC₀.trans_le hy.1)).sub (hasDerivAt_id y))
      (fun y hy => sub_nonneg.mpr (entropyVariance_curvature_one hk0 hk1 (hC₀.trans_le hy.1)))
    linarith
  have hd (x : ℝ) (hx : C₀ ≤ x) :
      HasDerivAt (fun y => entropyVarianceSlack k B y -
        entropyVarianceSlope k B C₀ * (y - C₀) - (y - C₀)^2 / 2)
        (entropyVarianceSlope k B x - entropyVarianceSlope k B C₀ - (x - C₀)) x := by
    convert! ((entropyVarianceSlack_hasDerivAt hk0 (hC₀.trans_le hx)).sub
      (((hasDerivAt_id x).sub_const C₀).const_mul (entropyVarianceSlope k B C₀))).sub
        ((((hasDerivAt_id x).sub_const C₀).pow 2).div_const 2) using 1
    dsimp
    ring
  have h := value_le_of_deriv_nonneg hC (fun x hx => hd x hx.1)
    (fun x hx => by linarith [hslope x hx.1])
  simp only [sub_self, mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_zero] at h
  linarith

theorem entropyVariance_at_base {k a : ℝ} (hk : 0 < k) (ha : 0 < a) :
    entropyVarianceSlack k (1 - a) (1 + k * a) =
      1 / k - 1 + log k + 2 * a - a ^ 2 - 2 * log (1 + k * a) := by
  have hC : 0 < 1 + k * a := by positivity
  unfold entropyVarianceSlack
  rw [log_div (pow_ne_zero 2 hC.ne') hk.ne', log_pow]
  field_simp
  ring

theorem entropyVariance_at_base_lower {k a : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (ha : 0 ≤ a) :
    -(2 * a ^ 3 / 3) ≤ entropyVarianceSlack k (1 - a) (1 + k * a) := by
  have hC : 0 < 1 + k * a := by positivity
  have heq : entropyVarianceSlack k (1 - a) (1 + k * a) =
      1 / k - 1 + log k + 2 * a - a ^ 2 - 2 * log (1 + k * a) := by
    unfold entropyVarianceSlack
    rw [log_div (pow_ne_zero 2 hC.ne') hk0.ne', log_pow]
    field_simp
    ring
  rw [heq]
  have hlogk := one_sub_inv_le_log_of_pos hk0
  have hlog := log_le_log hC (show 1 + k * a ≤ 1 + a by nlinarith)
  have hcubic := log_one_add_cubic_upper ha
  simp only [one_div] at *
  linarith

theorem entropyVarianceSlope_at_base {k a : ℝ} (hk : 0 < k) (ha : 0 ≤ a) :
    entropyVarianceSlope k (1 - a) (1 + k * a) = 2 / k - 2 / (1 + k * a) := by
  unfold entropyVarianceSlope
  field_simp
  ring

theorem entropyVarianceSlope_at_base_lower {k a : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (ha : 0 ≤ a) :
    2 * a / (1 + a) ≤ entropyVarianceSlope k (1 - a) (1 + k * a) := by
  rw [entropyVarianceSlope_at_base hk0 ha]
  have hkp : 0 < 1 + k * a := by positivity
  have hap : 0 < 1 + a := by positivity
  have heq : 1 / k - 1 / (1 + k * a) - a / (1 + a) =
      (1 - k) * (1 + a + k * a ^ 2) / (k * (1 + k * a) * (1 + a)) := by
    field_simp
    ring
  have hnonneg : 0 ≤ 1 / k - 1 / (1 + k * a) - a / (1 + a) := by
    rw [heq]
    positivity
  have h2 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnonneg
  ring_nf at h2 ⊢
  linarith

theorem entropyVariance_pos_large {k a C : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hC : 1 + k * a ≤ C)
    (hlarge : (1 + k) * a ^ 3 / 3 ≤ (C - (1 + k * a)) ^ 2) :
    0 < entropyVarianceSlack k (1 - a) C := by
  let Δ := C - (1 + k * a)
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr hC
  have hΔsq : a ^ 3 / 3 ≤ Δ ^ 2 := by
    dsimp [Δ]
    have hp := mul_nonneg hk0.le (pow_nonneg ha0.le 3)
    nlinarith
  have hΔlower : a ^ 2 / 2 < Δ := by
    by_contra h
    have hle : Δ ≤ a ^ 2 / 2 := le_of_not_gt h
    have hsq := mul_self_le_mul_self hΔ hle
    have hp := mul_pos (pow_pos ha0 3) (show 0 < 4 - 3 * a by linarith)
    nlinarith
  have hlinslope : a ≤ 2 * a / (1 + a) := by
    rw [le_div_iff₀ (show 0 < 1 + a by positivity)]
    nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr ha1.le)]
  have hlinear : a ^ 3 / 2 < entropyVarianceSlope k (1 - a) (1 + k * a) * Δ := by
    have hprod := mul_le_mul_of_nonneg_right
      (hlinslope.trans (entropyVarianceSlope_at_base_lower hk0 hk1 ha0.le)) hΔ
    have hstrict := mul_lt_mul_of_pos_left hΔlower ha0
    nlinarith
  have ht := entropyVariance_taylor_lower (B := 1 - a) hk0 hk1
    (show 0 < 1 + k * a by positivity) hC
  have hb := entropyVariance_at_base_lower hk0 hk1 ha0.le
  change entropyVarianceSlack k (1 - a) (1 + k * a) +
    entropyVarianceSlope k (1 - a) (1 + k * a) * Δ + Δ ^ 2 / 2 ≤ _ at ht
  linarith

theorem entropy_transport_complete_square {k B C u : ℝ} (hk : 0 < k) :
    u * (C - B) - k * u ^ 2 / 2 - B * entropyEll u -
      (C - B) ^ 2 / (2 * (1 + k)) =
    entropySlack B u - (C - B - (1 + k) * u) ^ 2 / (2 * (1 + k)) := by
  unfold entropySlack
  field_simp
  ring

theorem entropy_scalar_optimization {k B C R : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hB0 : 0 < B) (hB1 : B < 1) (hR : 0 ≤ R)
    (htransport : ∀ u < 1, u * (C - B) - k * u ^ 2 / 2 - B * entropyEll u ≤ R)
    (hvariance : 1 < C → C ^ 2 / k - 1 - log (C ^ 2 / k) ≤ 2 * R) :
    (C - B) ^ 2 / (2 * (1 + k)) ≤ R ∧
      (C ≠ B → (C - B) ^ 2 / (2 * (1 + k)) < R) := by
  have hkp : 0 < 1 + k := by linarith
  have hstrict (hCB : C ≠ B) : (C - B) ^ 2 / (2 * (1 + k)) < R := by
    let a := 1 - B
    have ha0 : 0 < a := sub_pos.mpr hB1
    have ha1 : a < 1 := by dsimp [a]; linarith
    by_cases hsmall : (C - B) / (1 + k) ≤ a
    · let u := (C - B) / (1 + k)
      have hu1 : u < 1 := hsmall.trans_lt ha1
      have hu0 : u ≠ 0 := div_ne_zero (sub_ne_zero.mpr hCB) hkp.ne'
      have hs := entropySlack_pos hB0.le hB1 hsmall hu1 hu0
      have ht := htransport u hu1
      have he := entropy_transport_complete_square (B := B) (C := C) (u := u) hk0
      have hzero : C - B - (1 + k) * u = 0 := by dsimp [u]; field_simp; ring
      rw [hzero] at he
      norm_num at he
      linarith
    · have hC : 1 + k * a < C := by
        have ht := (lt_div_iff₀ hkp).mp (lt_of_not_ge hsmall)
        dsimp [a] at *
        nlinarith
      by_cases hlarge : (1 + k) * a ^ 3 / 3 ≤ (C - (1 + k * a)) ^ 2
      · have hf := entropyVariance_pos_large hk0 hk1 ha0 ha1 hC.le hlarge
        have hv := hvariance (by have hp := mul_pos hk0 ha0; linarith)
        have hB : 1 - a = B := by dsimp [a]; ring
        rw [hB] at hf
        unfold entropyVarianceSlack at hf
        have he : (C - B) ^ 2 / (1 + k) = 2 * ((C - B) ^ 2 / (2 * (1 + k))) := by field_simp
        rw [he] at hf
        linarith
      · have hs := entropySlack_cubic_lower ha0.le ha1
        have hB : 1 - a = B := by dsimp [a]; ring
        rw [hB] at hs
        have ht := htransport a ha1
        have he := entropy_transport_complete_square (B := B) (C := C) (u := a) hk0
        have hdelta : C - B - (1 + k) * a = C - (1 + k * a) := by dsimp [a]; ring
        rw [hdelta] at he
        have hbound : (C - (1 + k * a)) ^ 2 / (2 * (1 + k)) < a ^ 3 / 6 := by
          rw [div_lt_iff₀ (by positivity : 0 < 2 * (1 + k))]
          linarith [lt_of_not_ge hlarge]
        linarith
  refine ⟨?_, hstrict⟩
  by_cases hCB : C = B
  · simpa [hCB] using hR
  · exact (hstrict hCB).le

theorem entropy_variance_function_mono {w v : ℝ} (hw : 1 ≤ w) (hv : w ≤ v) :
    w - 1 - log w ≤ v - 1 - log v := by
  apply value_le_of_deriv_nonneg hv
    (g := fun x => 1 - 1 / x)
  · intro x hx
    have hxp : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hw.trans hx.1)
    convert! ((hasDerivAt_id x).sub_const 1).sub ((hasDerivAt_id x).log hxp.ne') using 1
  · intro x hx
    have hx1 : 1 ≤ x := hw.trans hx.1
    rw [sub_nonneg, div_le_one (by linarith : 0 < x)]
    exact hx1

theorem entropy_variance_scale {j w : ℝ} (hj0 : 0 < j) (hj1 : j ≤ 1) (hw : 1 ≤ w) :
    w - 1 - log w ≤ j * (w / j - 1 - log (w / j)) := by
  have hwp : 0 < w := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hw
  rw [log_div hwp.ne' hj0.ne']
  have hlog := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos hj0) hj0.le
  have hextra := mul_nonneg (sub_nonneg.mpr hj1) (log_nonneg hw)
  have heq : j * (1 - j⁻¹) = j - 1 := by field_simp
  rw [heq] at hlog
  have hcancel : j * (w / j) = w := mul_div_cancel₀ w hj0.ne'
  nlinarith

theorem entropy_variance_scaled_lower {j k C v D : ℝ}
    (hj0 : 0 < j) (hj1 : j ≤ 1) (hk0 : 0 < k) (hk1 : k ≤ 1) (hC : 1 < C)
    (hcv : C ^ 2 / (j * k) ≤ v) (hD : (v - 1 - log v) / 2 ≤ D) :
    C ^ 2 / k - 1 - log (C ^ 2 / k) ≤ 2 * (j * D) := by
  have hw : 1 ≤ C ^ 2 / k := by rw [le_div_iff₀ hk0]; nlinarith
  have hwj : 1 ≤ C ^ 2 / (j * k) := by
    rw [le_div_iff₀ (mul_pos hj0 hk0)]
    nlinarith [mul_le_mul_of_nonneg_right hj1 hk0.le]
  have hm := entropy_variance_function_mono hwj hcv
  have hs := entropy_variance_scale hj0 hj1 hw
  have heq : C ^ 2 / k / j = C ^ 2 / (j * k) := by field_simp
  rw [heq] at hs
  have hmj := mul_le_mul_of_nonneg_left hm hj0.le
  have hdj := mul_le_mul_of_nonneg_left hD hj0.le
  linarith

end SKGap

end
end
end

end OAI
