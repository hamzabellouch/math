import OAI.InformationTheory.SoftChannel.Canonical

namespace OAI

section

noncomputable section
open Set
namespace SoftChannel204

def thinningPolynomial (t u : ℝ) : ℝ :=
  3 * (2 - t * u - t ^ 2 * u ^ 2) -
    (2 * (2 + t * u) * (1 - t) - 3 * t * u ^ 2 * (1 - t * u)) *
      (1 + t * (3 - u))

theorem thinningPolynomial_pos (t u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (ht0 : 0 ≤ t) (htu : t * (1 + u) ≤ 1) : 0 < thinningPolynomial t u := by
  let a := 12 - 8 * u + 8 * u ^ 2 - 6 * u ^ 3
  let b := 3 * u ^ 2 - u - 8
  let c := u * (3 - u) * (2 - 3 * u ^ 2)
  have hc : -u * (1 + u) ≤ c := by
    have h : 0 ≤ u * (1 - u) * (7 + 6 * u - 3 * u ^ 2) := by
      have : u ^ 2 ≤ u := by nlinarith
      apply mul_nonneg (mul_nonneg hu0 (sub_nonneg.mpr hu1))
      nlinarith
    dsimp [c]
    nlinarith
  have hct : -u ≤ c * t := by
    calc
      -u ≤ -u * (t * (1 + u)) := by nlinarith
      _ = (-u * (1 + u)) * t := by ring
      _ ≤ c * t := mul_le_mul_of_nonneg_right hc ht0
  have hp : 2 + b * t + (a - u) * t ^ 2 ≤ thinningPolynomial t u := by
    have h := mul_nonneg (show 0 ≤ c * t + u by linarith) (sq_nonneg t)
    dsimp [thinningPolynomial, a, b, c] at *
    nlinarith
  have hd : 4 ≤ 8 * (a - u) - b ^ 2 := by
    have h : 0 ≤ (1 - u) * (2 * (5 * u - 3) ^ 2 + u ^ 2 * (1 + 9 * u) + 10) :=
      mul_nonneg (sub_nonneg.mpr hu1) (by positivity)
    dsimp [a, b]
    nlinarith
  have hd' := mul_le_mul_of_nonneg_right hd (sq_nonneg t)
  by_cases ht : t = 0
  · subst t
    norm_num [thinningPolynomial]
  · have hs : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    nlinarith [sq_nonneg (4 + b * t)]

theorem thinning_cutoff_bound {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    4 * Real.log 2 * x ≤ (3 + x) * Real.log (1 + x) := by
  let f : ℝ → ℝ := fun y => (3 + y) * Real.log (1 + y) - 4 * Real.log 2 * y
  let f' : ℝ → ℝ := fun y =>
    Real.log (1 + y) + (3 + y) / (1 + y) - 4 * Real.log 2
  let f'' : ℝ → ℝ := fun y => (y - 1) / (1 + y) ^ 2
  have hd (y : ℝ) (hy : -1 < y) : HasDerivAt f (f' y) y := by
    have hn : 1 + y ≠ 0 := by linarith
    convert! ((((hasDerivAt_id y).const_add 3).mul
      (((hasDerivAt_id y).const_add 1).log hn)).sub
      ((hasDerivAt_id y).const_mul (4 * Real.log 2))) using 1;
      simp [f', div_eq_mul_inv]
  have hd' (y : ℝ) (hy : -1 < y) : HasDerivAt f' (f'' y) y := by
    have hn : 1 + y ≠ 0 := by linarith
    convert! ((((hasDerivAt_id y).const_add 1).log hn).add
      (((hasDerivAt_id y).const_add 3).div
        ((hasDerivAt_id y).const_add 1) hn)).sub_const (4 * Real.log 2) using 1
    dsimp [f'']
    field_simp
    ring
  have hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) f := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := f') (f'' := f'') (convex_Icc 0 1)
    · intro y hy
      exact (hd y (by linarith [hy.1])).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hd y (by linarith [hy.1])).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hd' y (by linarith [hy.1])).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hy.2]) (sq_nonneg _)
  have h := hc.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
    (show 0 ≤ 1 - x by linarith [hx.2]) hx.1 (by ring : 1 - x + x = 1)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at h
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 0 := by norm_num [f]
  rw [hf0, hf1] at h
  dsimp [f] at h
  linarith

def clipKernel (β v : ℝ) : ℝ := max (v - β) 0 / v ^ 2

theorem clipKernel_nonneg (β v : ℝ) : 0 ≤ clipKernel β v :=
  div_nonneg (le_max_right _ _) (sq_nonneg _)

theorem clipKernel_of_le {β v : ℝ} (h : v ≤ β) : clipKernel β v = 0 := by
  simp [clipKernel, max_eq_right (sub_nonpos.mpr h)]

theorem clipKernel_eq {β v : ℝ} (h : β ≤ v) :
    clipKernel β v = (v - β) / v ^ 2 := by
  rw [clipKernel, max_eq_left (sub_nonneg.mpr h)]

theorem clipKernel_min {β u v : ℝ} (hβ0 : 0 ≤ β) (hu0 : 0 < u)
    (huv : u ≤ v) (hv1 : v ≤ 1) :
    min (clipKernel β u) (1 - β) ≤ clipKernel β v := by
  by_cases huβ : u ≤ β
  · rw [clipKernel_of_le huβ]
    exact (min_le_left _ _).trans (clipKernel_nonneg _ _)
  have hβu : β < u := lt_of_not_ge huβ
  have hv0 : 0 < v := hu0.trans_le huv
  have hβv : β ≤ v := hβu.le.trans huv
  have hc : ConcaveOn ℝ (Ici (0 : ℝ)) (fun t => t - β * t ^ 2) := by
    convert! (concaveOn_id (convex_Ici (0 : ℝ))).sub
      ((convexOn_pow (𝕜 := ℝ) 2).smul hβ0) using 1
  have hi : (1 / v : ℝ) ∈ Icc 1 (1 / u) := by
    constructor
    · exact (le_div_iff₀ hv0).mpr (by simpa using hv1)
    · exact one_div_le_one_div_of_le hu0 huv
  have h := hc.min_le_of_mem_Icc (show (1 : ℝ) ∈ Ici 0 by norm_num)
    (show 1 / u ∈ Ici (0 : ℝ) from (one_div_pos.mpr hu0).le) hi
  have he (w : ℝ) (hw : w ≠ 0) :
      1 / w - β * (1 / w) ^ 2 = (w - β) / w ^ 2 := by
    field_simp
  simp only [one_pow, mul_one] at h
  rw [he u hu0.ne', he v hv0.ne', min_comm] at h
  rwa [clipKernel_eq hβu.le, clipKernel_eq hβv]

theorem thinning_endpoint_algebra {t u : ℝ} (ht0 : 0 ≤ t) (hu0 : 0 < u)
    (hu1 : u ≤ 1) (htu : t * (1 + u) ≤ 1) :
    let b := t * u
    let x := 3 * b / (4 - b)
    ((1 + x) * ((u - b) / u ^ 2) - x * (1 - b)) *
      ((4 * x + (1 - x) * u) / ((1 - x) * (1 + x))) ≤ 3 / 2 := by
  dsimp only
  have ht : t * u < 1 := by
    by_cases he : t = 0
    · simp [he]
    · have : 0 < t := lt_of_le_of_ne ht0 (Ne.symm he)
      nlinarith
  have h4 : 4 - t * u ≠ 0 := by linarith
  have h1 : 1 - t * u ≠ 0 := by linarith
  have h2 : 2 + t * u ≠ 0 := by positivity
  have hp := (thinningPolynomial_pos t u hu0.le hu1 ht0 htu).le
  have hd : 0 < 2 * (1 - t * u) * (2 + t * u) := by positivity
  have hf : 1 - 3 * (t * u) / (4 - t * u) ≠ 0 := by
    intro he
    have he' := (div_eq_iff h4).mp (show 3 * (t * u) / (4 - t * u) = 1 by linarith)
    nlinarith
  have hf' : 1 + 3 * (t * u) / (4 - t * u) ≠ 0 := by
    have : 0 ≤ 3 * (t * u) / (4 - t * u) := div_nonneg (by positivity) (by linarith)
    positivity
  have hid : 3 / 2 -
      ((1 + 3 * (t * u) / (4 - t * u)) * ((u - t * u) / u ^ 2) -
        3 * (t * u) / (4 - t * u) * (1 - t * u)) *
        ((4 * (3 * (t * u) / (4 - t * u)) +
          (1 - 3 * (t * u) / (4 - t * u)) * u) /
          ((1 - 3 * (t * u) / (4 - t * u)) * (1 + 3 * (t * u) / (4 - t * u)))) =
      thinningPolynomial t u / (2 * (1 - t * u) * (2 + t * u)) := by
    unfold thinningPolynomial
    have hden : 16 - t * u * 8 - t ^ 2 * u ^ 2 * 8 ≠ 0 := by
      have he : 16 - t * u * 8 - t ^ 2 * u ^ 2 * 8 =
          8 * (1 - t * u) * (2 + t * u) := by ring
      rw [he]
      exact mul_ne_zero (mul_ne_zero (by norm_num) h1) h2
    field_simp [hu0.ne', h4, hf, hf', h1, h2, hden]
    ring_nf
    field_simp [hden]
    ring
  have hnonneg := div_nonneg hp hd.le
  rw [← hid] at hnonneg
  linarith

theorem thinning_hard_bound {x u β : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hβ1 : β ≤ 1)
    (hcut : 4 * x / (3 + x) ≤ β) (hh : 1 - β < clipKernel β u) :
    ((1 + x) * clipKernel β u - x * (1 - β)) *
      ((4 * x + (1 - x) * u) / ((1 - x) * (1 + x))) ≤ 3 / 2 := by
  let b : ℝ := 4 * x / (3 + x)
  have hb0 : 0 ≤ b := div_nonneg (by positivity) (by positivity)
  have hbβ : b ≤ β := hcut
  have hβ0 : 0 ≤ β := hb0.trans hbβ
  have hbu : β < u := by
    by_contra hn
    rw [clipKernel_of_le (le_of_not_gt hn)] at hh
    linarith
  have hk : clipKernel β u * u ^ 2 = u - β := by
    rw [clipKernel_eq hbu.le, div_mul_cancel₀ _ (pow_ne_zero _ hu0.ne')]
  have hp : 0 < (1 - u) * (u - β * (1 + u)) := by
    have hm := mul_lt_mul_of_pos_right hh (sq_pos_of_pos hu0)
    rw [hk] at hm
    nlinarith
  have hcore : β * (1 + u) < u := by
    by_contra hn
    have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu1)
      (show u - β * (1 + u) ≤ 0 by linarith)
    linarith
  have hbcore : b * (1 + u) ≤ u :=
    (mul_le_mul_of_nonneg_right hbβ (by positivity)).trans hcore.le
  have hb1 : b < 1 := by nlinarith
  let t := b / u
  have ht0 : 0 ≤ t := div_nonneg hb0 hu0.le
  have htu : t * u = b := div_mul_cancel₀ _ hu0.ne'
  have ht : t * (1 + u) ≤ 1 := by
    dsimp [t]
    rw [div_mul_eq_mul_div, div_le_iff₀ hu0]
    simpa using hbcore
  have h4 : 4 - b ≠ 0 := by linarith
  have hbx : 3 * b / (4 - b) = x := by
    apply (div_eq_iff h4).mpr
    dsimp [b]
    field_simp
    ring
  have hend := thinning_endpoint_algebra ht0 hu0 hu1 ht
  dsimp only at hend
  rw [htu, hbx] at hend
  have hcoeff : 0 ≤ (1 + x) / u ^ 2 - x := by
    have hsq : u ^ 2 ≤ 1 := by nlinarith
    have hle : x ≤ (1 + x) / u ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hu0)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsq hx0]
    linarith
  have hcomp : (1 + x) * clipKernel β u - x * (1 - β) ≤
      (1 + x) * ((u - b) / u ^ 2) - x * (1 - b) := by
    rw [clipKernel_eq hbu.le]
    have h := mul_nonneg (sub_nonneg.mpr hbβ) hcoeff
    simp only [div_eq_mul_inv] at *
    nlinarith
  have hfac : 0 ≤ (4 * x + (1 - x) * u) / ((1 - x) * (1 + x)) := by
    apply div_nonneg <;> positivity
  exact (mul_le_mul_of_nonneg_right hcomp hfac).trans hend

theorem thinning_derivative_product {x a s β : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (ha1 : 1 ≤ a) (hap : a ≤ 1 + x) (hs0 : 0 ≤ s)
    (hsg : s < (1 - x) / (1 + x)) (hβ1 : β ≤ 1)
    (hcut : 4 * x / (3 + x) ≤ β) :
    let u := 2 - a * (1 + s)
    let v := u + s
    (a * clipKernel β u - (a - 1) * clipKernel β v) *
      ((1 + x) / (1 - x) - s) ≤ 3 / 2 := by
  let u := 2 - a * (1 + s)
  let v := u + s
  let Y := (1 + x) / (1 - x) - s
  change (a * clipKernel β u - (a - 1) * clipKernel β v) * Y ≤ 3 / 2
  have hp : 0 < 1 + x := by positivity
  have hσ : 0 < 1 - x := by linarith
  have ha : 0 < a := by linarith
  have hs : (1 + x) * s < 1 - x := by
    have := (lt_div_iff₀ hp).mp hsg
    nlinarith
  have hu0 : 0 < u := by
    have hh := mul_le_mul_of_nonneg_right hap (show 0 ≤ 1 + s by positivity)
    dsimp [u]
    nlinarith
  have huv : u ≤ v := by dsimp [v]; linarith
  have hv1 : v ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ 1 + s by positivity)
    dsimp [v, u]
    nlinarith
  have hu1 : u ≤ 1 := huv.trans hv1
  have hs1 : s < 1 := by nlinarith [mul_nonneg hx0 hs0]
  have hratio : 1 ≤ (1 + x) / (1 - x) := by
    apply (le_div_iff₀ hσ).mpr
    linarith
  have hY : 0 < Y := by dsimp [Y]; linarith
  have hb0 : 0 ≤ β :=
    (div_nonneg (show 0 ≤ 4 * x by positivity) (show 0 ≤ 3 + x by positivity)).trans hcut
  have hc0 : 0 ≤ 1 - β := by linarith
  have hmin := clipKernel_min hb0 hu0 huv hv1
  by_cases heasy : clipKernel β u ≤ 1 - β
  · rw [min_eq_left heasy] at hmin
    have hD : a * clipKernel β u - (a - 1) * clipKernel β v ≤ 1 - β := by
      have := mul_nonneg (show 0 ≤ a - 1 by linarith) (sub_nonneg.mpr hmin)
      nlinarith
    have hc : (1 - β) * (2 * (1 + x)) ≤ 3 * (1 - x) := by
      have hb := (div_le_iff₀ (show 0 < 3 + x by positivity)).mp hcut
      have hh := mul_le_mul_of_nonneg_left
        (show 2 * (1 + x) ≤ 3 + x by linarith) hc0
      nlinarith
    calc
      _ ≤ (1 - β) * Y := mul_le_mul_of_nonneg_right hD hY.le
      _ ≤ (1 - β) * ((1 + x) / (1 - x)) :=
        mul_le_mul_of_nonneg_left (by dsimp [Y]; linarith) hc0
      _ = ((1 - β) * (1 + x)) / (1 - x) := by ring
      _ ≤ 3 / 2 := (div_le_iff₀ hσ).mpr (by nlinarith)
  · have hhard : 1 - β < clipKernel β u := lt_of_not_ge heasy
    rw [min_eq_right hhard.le] at hmin
    have hD : a * clipKernel β u - (a - 1) * clipKernel β v ≤
        a * (clipKernel β u - (1 - β)) + (1 - β) := by
      have := mul_nonneg (show 0 ≤ a - 1 by linarith) (sub_nonneg.mpr hmin)
      nlinarith
    have hfirst : a * (clipKernel β u - (1 - β)) + (1 - β) ≤
        (1 + x) * (clipKernel β u - (1 - β)) + (1 - β) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hap) (sub_nonneg.mpr hhard.le)]
    have hid : Y = 2 / (1 - x) - (2 - u) / a := by
      dsimp [Y, u]
      field_simp
      ring
    have hidp : 2 / (1 - x) - (2 - u) / (1 + x) =
        (4 * x + (1 - x) * u) / ((1 - x) * (1 + x)) := by
      field_simp
      ring
    have hYle : Y ≤ (4 * x + (1 - x) * u) / ((1 - x) * (1 + x)) := by
      rw [hid, ← hidp]
      exact sub_le_sub_left (div_le_div_of_nonneg_left (by linarith) ha hap) _
    have hbound := thinning_hard_bound hx0 hx1 hu0 hu1 hβ1 hcut hhard
    calc
      _ ≤ (a * (clipKernel β u - (1 - β)) + (1 - β)) * Y :=
        mul_le_mul_of_nonneg_right hD hY.le
      _ ≤ ((1 + x) * (clipKernel β u - (1 - β)) + (1 - β)) *
          ((4 * x + (1 - x) * u) / ((1 - x) * (1 + x))) :=
        mul_le_mul hfirst hYle hY.le
          (add_nonneg (mul_nonneg hp.le (sub_nonneg.mpr hhard.le)) hc0)
      _ = ((1 + x) * clipKernel β u - x * (1 - β)) *
          ((4 * x + (1 - x) * u) / ((1 - x) * (1 + x))) := by ring
      _ ≤ 3 / 2 := hbound

open MeasureTheory

theorem continuousAt_clipKernel (β : ℝ) {v : ℝ} (hv : 0 < v) :
    ContinuousAt (clipKernel β) v := by
  unfold clipKernel
  exact ((continuousAt_id.sub continuousAt_const).max continuousAt_const).div
    (continuousAt_id.pow 2) (pow_ne_zero _ hv.ne')

theorem intervalIntegrable_clipKernel (β : ℝ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (clipKernel β) volume u v := by
  apply ContinuousOn.intervalIntegrable
  intro w hw
  exact (continuousAt_clipKernel β
    (lt_of_lt_of_le (lt_min hu hv) hw.1)).continuousWithinAt

def clipPrimitive (β w : ℝ) : ℝ := ∫ v in (1 : ℝ)..w, clipKernel β v

theorem hasDerivAt_clipPrimitive (β : ℝ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (clipPrimitive β) (clipKernel β w) w := by
  apply intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_clipKernel β (by norm_num) hw)
  · exact ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun v hv => continuousAt_clipKernel β hv) w hw
  · exact continuousAt_clipKernel β hw

theorem thinning_interval_aux {x β u z : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hβ1 : β ≤ 1) (hcut : 4 * x / (3 + x) ≤ β)
    (hz0 : 0 ≤ z) (hzg : z < (1 - x) / (1 + x))
    (hulo : 1 - x - (1 + x) * z ≤ u) (huhi : u ≤ 1 - z) :
    (∫ v in u..u+z, clipKernel β v) ≤
      -(3 / 2 : ℝ) * Real.log (1 - ((1 - x) / (1 + x)) * z) := by
  let γ := (1 - x) / (1 + x)
  let a := (2 - u) / (1 + z)
  let U : ℝ → ℝ := fun s => 2 - a * (1 + s)
  let V : ℝ → ℝ := fun s => U s + s
  let f : ℝ → ℝ := fun s => clipPrimitive β (V s) - clipPrimitive β (U s) +
    (3 / 2) * Real.log (1 - γ * s)
  let f' : ℝ → ℝ := fun s =>
    a * clipKernel β (U s) - (a - 1) * clipKernel β (V s) -
      (3 / 2) * γ / (1 - γ * s)
  have hp : 0 < 1 + x := by positivity
  have hσ : 0 < 1 - x := by linarith
  have hγ0 : 0 < γ := div_pos hσ hp
  have hγ1 : γ ≤ 1 := by dsimp [γ]; exact (div_le_one hp).mpr (by linarith)
  have hz1 : z < 1 := hzg.trans_le hγ1
  have ha1 : 1 ≤ a := (le_div_iff₀ (by positivity : 0 < 1 + z)).mpr (by linarith)
  have hap : a ≤ 1 + x := by
    apply (div_le_iff₀ (by positivity : 0 < 1 + z)).mpr
    nlinarith
  have bounds (s : ℝ) (hs : s ∈ Icc 0 z) :
      0 < U s ∧ U s ≤ V s ∧ V s ≤ 1 ∧ 0 < 1 - γ * s := by
    have hsγ : s < γ := hs.2.trans_lt hzg
    have hps := (lt_div_iff₀ hp).mp hsγ
    have ha := mul_le_mul_of_nonneg_right hap (show 0 ≤ 1 + s by linarith [hs.1])
    have hb := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ 1 + s by linarith [hs.1])
    have hγs := mul_le_mul_of_nonneg_right hγ1 hs.1
    dsimp [U, V]
    exact ⟨by nlinarith, by linarith [hs.1], by nlinarith,
      by nlinarith [hs.2]⟩
  have hd (s : ℝ) (hs : s ∈ Icc 0 z) : HasDerivAt f (f' s) s := by
    obtain ⟨hu0, huv, hv1, hlog⟩ := bounds s hs
    have hu : HasDerivAt U (-a) s := by
      convert! (((hasDerivAt_id s).const_add 1).const_mul a).const_sub 2 using 1;
        simp
    have hv : HasDerivAt V (1 - a) s := by
      convert! hu.add (hasDerivAt_id s) using 1; ring
    have hl := ((((hasDerivAt_id s).const_mul γ).const_sub 1).log hlog.ne').const_mul
      (3 / 2 : ℝ)
    convert! (((hasDerivAt_clipPrimitive β (hu0.trans_le huv)).comp s hv).sub
      ((hasDerivAt_clipPrimitive β hu0).comp s hu)).add hl using 1;
      simp [f']; ring
  have hnonpos (s : ℝ) (hs : s ∈ Icc 0 z) : f' s ≤ 0 := by
    have hb := thinning_derivative_product hx0 hx1 ha1 hap hs.1
      (hs.2.trans_lt hzg) hβ1 hcut
    change (a * clipKernel β (U s) - (a - 1) * clipKernel β (V s)) *
      ((1 + x) / (1 - x) - s) ≤ 3 / 2 at hb
    have hY : 0 < (1 + x) / (1 - x) - s := by
      have hr : 1 ≤ (1 + x) / (1 - x) := (le_div_iff₀ hσ).mpr (by linarith)
      linarith [hs.2]
    have hid : (3 / 2 : ℝ) * γ / (1 - γ * s) =
        (3 / 2 : ℝ) / ((1 + x) / (1 - x) - s) := by
      dsimp [γ]
      field_simp
    have hb' := (le_div_iff₀ hY).mpr hb
    dsimp [f']
    rw [hid]
    linarith
  have hanti : AntitoneOn f (Icc 0 z) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Icc _ _)
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hd s ⟨hs.1.le, hs.2.le⟩).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact hnonpos s ⟨hs.1.le, hs.2.le⟩
  have hle := hanti (show (0 : ℝ) ∈ Icc 0 z from ⟨le_rfl, hz0⟩)
    (show z ∈ Icc 0 z from ⟨hz0, le_rfl⟩) hz0
  have hU : U z = u := by
    dsimp [U, a]
    field_simp
    ring
  have hV : V z = u + z := by simp [V, hU]
  have hu0 : 0 < u := hU ▸ (bounds z ⟨hz0, le_rfl⟩).1
  have hv0 : 0 < u + z := by linarith
  have hprim : clipPrimitive β (u + z) - clipPrimitive β u =
      ∫ v in u..u+z, clipKernel β v := by
    have hh := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_clipKernel β (show (0 : ℝ) < 1 by norm_num) hu0)
      (intervalIntegrable_clipKernel β hu0 hv0)
    dsimp [clipPrimitive]
    linarith
  dsimp [f] at hle
  rw [hU, hV, hprim] at hle
  simp [V] at hle
  linarith

theorem thinning_interval {x u z : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hz0 : 0 ≤ z) (hzg : z < (1 - x) / (1 + x))
    (hulo : 1 - x - (1 + x) * z ≤ u) (huhi : u ≤ 1 - z) :
    (∫ v in u..u+z, clipKernel (Real.log (1 + x) / Real.log 2) v) ≤
      -(3 / 2 : ℝ) * Real.log (1 - ((1 - x) / (1 + x)) * z) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβ1 : Real.log (1 + x) / Real.log 2 ≤ 1 := by
    apply (div_le_one hL).mpr
    exact Real.log_le_log (by positivity) (by linarith)
  have hb := thinning_cutoff_bound ⟨hx0, hx1.le⟩
  have hcut : 4 * x / (3 + x) ≤ Real.log (1 + x) / Real.log 2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 3 + x) hL).mpr
    nlinarith
  exact thinning_interval_aux hx0 hx1 hβ1 hcut hz0 hzg hulo huhi

end SoftChannel204
end
end

end OAI
