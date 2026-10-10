import OAI.Analysis.Steinitz.Model

namespace OAI

/-! Scalar potentials and spectral endpoint inequalities. -/

namespace EuclideanSteinitz.MatrixEnergy

open Matrix
open scoped MatrixOrder

noncomputable def exponent : ℝ := 3 / 2

noncomputable def cutoff (x : ℝ) : ℝ :=
  if x ≤ 1 / 2 then 0 else if x < 1 then 2 * x - 1 else
    if x ≤ 2 then 1 else if x < 4 then 2 - x / 2 else 0

noncomputable def weight (x : ℝ) : ℝ := min (x ^ exponent) x⁻¹

noncomputable def potential (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, weight u / u

noncomputable def gainPotential (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, u ^ (exponent - 1) / (1 + u) ^ exponent

noncomputable def sizeWeight (x : ℝ) : ℝ := min (x ^ (exponent - 1)) x⁻¹

noncomputable def scalarRemainder (x y : ℝ) : ℝ :=
  potential x - potential y + (y / x - 1) * (weight x + weight y) / 2

section Scalar

lemma exponent_pos : 0 < exponent := by norm_num [exponent]

lemma weight_of_le_one {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) :
    weight x = x ^ exponent := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num [weight, exponent, Real.zero_rpow]
  apply min_eq_left
  exact (Real.rpow_le_one hx.le h1 exponent_pos.le).trans (one_le_inv₀ hx |>.mpr h1)

lemma weight_of_one_le {x : ℝ} (hx : 1 ≤ x) : weight x = x⁻¹ := by
  apply min_eq_right
  exact (inv_le_one₀ (by linarith : 0 < x) |>.mpr hx).trans
    (Real.one_le_rpow hx exponent_pos.le)

lemma integrand_of_le_one {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) :
    weight x / x = x ^ (1 / 2 : ℝ) := by
  rw [weight_of_le_one hx h1]
  convert (Real.rpow_sub_one' hx (by norm_num [exponent] : exponent - 1 ≠ 0)).symm using 1
  norm_num [exponent]

lemma integrand_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    weight x / x = x ^ (-2 : ℝ) := by
  rw [weight_of_one_le hx]
  rw [show (-2 : ℝ) = -1 - 1 by norm_num,
    Real.rpow_sub_one (by linarith : x ≠ 0), Real.rpow_neg_one]

lemma potential_small {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) :
    potential x = x ^ exponent / exponent := by
  unfold potential
  calc
    _ = ∫ u in (0 : ℝ)..x, u ^ (1 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hx] at hu
      exact integrand_of_le_one hu.1 (hu.2.trans h1)
    _ = _ := by
      rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
      norm_num [exponent]

lemma small_integrable {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) :
    IntervalIntegrable (fun u => weight u / u) MeasureTheory.volume 0 x := by
  refine IntervalIntegrable.congr ?_
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < 1 / 2))
  intro u hu
  rw [Set.uIoc_of_le hx] at hu
  exact (integrand_of_le_one hu.1.le (hu.2.trans h1)).symm

lemma large_integrable {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable (fun u => weight u / u) MeasureTheory.volume 1 x := by
  have hz : (0 : ℝ) ∉ Set.uIcc 1 x := by
    rw [Set.uIcc_of_le hx]
    simp
  refine IntervalIntegrable.congr ?_
    (intervalIntegral.intervalIntegrable_rpow (Or.inr hz) :
      IntervalIntegrable (fun u : ℝ => u ^ (-2 : ℝ)) MeasureTheory.volume 1 x)
  intro u hu
  rw [Set.uIoc_of_le hx] at hu
  exact (integrand_of_one_le hu.1.le).symm

lemma potential_large {x : ℝ} (hx : 1 ≤ x) :
    potential x = 5 / 3 - x⁻¹ := by
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (small_integrable (show (0 : ℝ) ≤ 1 by norm_num) le_rfl) (large_integrable hx)
  have hint : (∫ u in (1 : ℝ)..x, weight u / u) = 1 - x⁻¹ := by
    calc
      _ = ∫ u in (1 : ℝ)..x, u ^ (-2 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hx] at hu
        exact integrand_of_one_le hu.1
      _ = _ := by
        rw [integral_rpow (Or.inr ⟨by norm_num, ?_⟩)]
        · norm_num [Real.rpow_neg_one]
          ring
        · rw [Set.uIcc_of_le hx]
          simp
  change potential 1 + _ = potential x at hsum
  rw [potential_small (by norm_num) le_rfl, hint] at hsum
  norm_num [exponent] at hsum
  linarith

lemma fourth_rpow_exponent {u : ℝ} (hu : 0 ≤ u) :
    (u ^ 4) ^ exponent = u ^ 6 := by
  rw [← Real.rpow_natCast_mul hu]
  norm_num [exponent, Real.rpow_natCast]

private noncomputable def rootWeight (u : ℝ) : ℝ :=
  if u ≤ 1 then u ^ 3 else (u ^ 2)⁻¹

private lemma weight_fourth {u : ℝ} (hu : 0 ≤ u) :
    weight (u ^ 4) = rootWeight u ^ 2 := by
  by_cases h : u ≤ 1
  · rw [weight_of_le_one (by positivity) (pow_le_one₀ hu h), fourth_rpow_exponent hu]
    simp only [rootWeight, ite_eq_left h]
    ring
  · rw [weight_of_one_le (one_le_pow₀ (le_of_not_ge h))]
    simp only [rootWeight, ite_eq_right h, inv_pow]
    ring

private lemma root_endpoint {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    ((rootWeight u) ^ 2 + (rootWeight v) ^ 2 -
      2 * rootWeight u * rootWeight v * (v / u) ^ 3) * (2 / 3) ≤
        potential (u ^ 4) - potential (v ^ 4) := by
  have up : 0 < u ^ 4 := by positivity
  have vp : 0 < v ^ 4 := by positivity
  by_cases hu1 : u ≤ 1 <;> by_cases hv1 : v ≤ 1
  · rw [potential_small up.le (pow_le_one₀ hu.le hu1),
      potential_small vp.le (pow_le_one₀ hv.le hv1),
      fourth_rpow_exponent hu.le, fourth_rpow_exponent hv.le]
    simp only [rootWeight, ite_eq_left hu1, ite_eq_left hv1, exponent]
    apply le_of_eq
    field_simp
    ring
  · rw [potential_small up.le (pow_le_one₀ hu.le hu1),
      fourth_rpow_exponent hu.le,
      potential_large (one_le_pow₀ (le_of_not_ge hv1))]
    simp only [rootWeight, ite_eq_left hu1, ite_eq_right hv1, exponent]
    have hn : 0 ≤ (v - 1) ^ 2 * (4 * v ^ 3 + 3 * v ^ 2 + 2 * v + 1) := by positivity
    have hid : u ^ 6 / (3 / 2) - (5 / 3 - (v ^ 4)⁻¹) -
        ((u ^ 3) ^ 2 + (v ^ 2)⁻¹ ^ 2 - 2 * u ^ 3 * (v ^ 2)⁻¹ * (v / u) ^ 3) * (2 / 3) =
        ((v - 1) ^ 2 * (4 * v ^ 3 + 3 * v ^ 2 + 2 * v + 1)) / (3 * v ^ 4) := by
      field_simp
      ring
    exact sub_nonneg.mp (hid ▸ div_nonneg hn (by positivity))
  · rw [potential_large (one_le_pow₀ (le_of_not_ge hu1)),
      potential_small vp.le (pow_le_one₀ hv.le hv1), fourth_rpow_exponent hv.le]
    simp only [rootWeight, ite_eq_right hu1, ite_eq_left hv1, exponent]
    have hu5 : 1 ≤ u ^ 5 := one_le_pow₀ (le_of_not_ge hu1)
    have hv6 : v ^ 6 ≤ 1 := pow_le_one₀ hv.le hv1
    have hn : 0 ≤ (u - 1) ^ 2 * (u ^ 3 + 2 * u ^ 2 + 3 * u + 4) +
        4 * (1 - v ^ 6) * (u ^ 5 - 1) := by positivity
    have hid : (5 / 3 - (u ^ 4)⁻¹) - v ^ 6 / (3 / 2) -
        ((u ^ 2)⁻¹ ^ 2 + (v ^ 3) ^ 2 - 2 * (u ^ 2)⁻¹ * v ^ 3 * (v / u) ^ 3) * (2 / 3) =
        ((u - 1) ^ 2 * (u ^ 3 + 2 * u ^ 2 + 3 * u + 4) +
          4 * (1 - v ^ 6) * (u ^ 5 - 1)) / (3 * u ^ 5) := by
      field_simp
      ring
    exact sub_nonneg.mp (hid ▸ div_nonneg hn (by positivity))
  · rw [potential_large (one_le_pow₀ (le_of_not_ge hu1)),
      potential_large (one_le_pow₀ (le_of_not_ge hv1))]
    simp only [rootWeight, ite_eq_right hu1, ite_eq_right hv1]
    have hn : 0 ≤ (u - v) ^ 2 * (u ^ 3 + 2 * u ^ 2 * v + 3 * u * v ^ 2 + 4 * v ^ 3) := by
      positivity
    have hid : (5 / 3 - (u ^ 4)⁻¹) - (5 / 3 - (v ^ 4)⁻¹) -
        ((u ^ 2)⁻¹ ^ 2 + (v ^ 2)⁻¹ ^ 2 - 2 * (u ^ 2)⁻¹ * (v ^ 2)⁻¹ * (v / u) ^ 3) * (2 / 3) =
        ((u - v) ^ 2 * (u ^ 3 + 2 * u ^ 2 * v + 3 * u * v ^ 2 + 4 * v ^ 3)) /
          (3 * u ^ 5 * v ^ 4) := by
      field_simp
      ring
    exact sub_nonneg.mp (hid ▸ div_nonneg hn (by positivity))

private lemma root_remainder {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (weight (u ^ 4) + weight (v ^ 4)) / 6 *
        (v / u - 1) ^ 2 * (3 * (v / u) ^ 2 + 2 * (v / u) + 1) ≤
      scalarRemainder (u ^ 4) (v ^ 4) := by
  have he := root_endpoint hu hv
  have hq : 0 ≤ (rootWeight u - rootWeight v) ^ 2 * (v / u) ^ 3 * (2 / 3) := by
    positivity
  dsimp only [scalarRemainder]
  rw [weight_fourth hu.le, weight_fourth hv.le, ← div_pow]
  nlinarith only [he, hq]

private lemma fourth_ratio_polynomial {t : ℝ} (ht : 0 ≤ t) :
    (t ^ 4 - 1) ^ 2 ≤ 4 * (t - 1) ^ 2 * (3 * t ^ 2 + 2 * t + 1) * (1 + t ^ 4) := by
  have h : 0 ≤ (t - 1) ^ 2 *
      (11 * t ^ 6 + 6 * t ^ 5 + t ^ 2 * (t - 2) ^ 2 + 5 * t ^ 2 + 6 * t + 3) := by
    positivity
  nlinarith only [h]

lemma weight_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ weight x := by
  exact le_min (Real.rpow_nonneg hx _) (inv_nonneg.mpr hx)

private lemma root_remainder_quadratic {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (weight (u ^ 4) + weight (v ^ 4)) * (u ^ 4 - v ^ 4) ^ 2 /
        (24 * u ^ 4 * (u ^ 4 + v ^ 4)) ≤ scalarRemainder (u ^ 4) (v ^ 4) := by
  let w := weight (u ^ 4) + weight (v ^ 4)
  have hw : 0 ≤ w := add_nonneg (weight_nonneg (by positivity)) (weight_nonneg (by positivity))
  calc
    _ = w * ((v / u) ^ 4 - 1) ^ 2 / (24 * (1 + (v / u) ^ 4)) := by
      dsimp only [w]
      field_simp
      ring
    _ ≤ w / 6 * (v / u - 1) ^ 2 * (3 * (v / u) ^ 2 + 2 * (v / u) + 1) := by
      apply (div_le_iff₀ (by positivity : 0 < 24 * (1 + (v / u) ^ 4))).mpr
      have h := mul_le_mul_of_nonneg_left (fourth_ratio_polynomial (by positivity : 0 ≤ v / u)) hw
      nlinarith only [h]
    _ ≤ _ := root_remainder hu hv

lemma scalar_remainder_lower {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (weight x + weight y) * (x - y) ^ 2 / (24 * x * (x + y)) ≤
      scalarRemainder x y := by
  let u := x ^ (1 / 4 : ℝ)
  let v := y ^ (1 / 4 : ℝ)
  have hu : 0 < u := Real.rpow_pos_of_pos hx _
  have hv : 0 < v := Real.rpow_pos_of_pos hy _
  have hux : u ^ 4 = x := by
    simpa only [u, one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (n := 4) hx.le (by norm_num)
  have hvy : v ^ 4 = y := by
    simpa only [v, one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (n := 4) hy.le (by norm_num)
  simpa only [hux, hvy] using root_remainder_quadratic hu hv

lemma scalar_remainder_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ scalarRemainder x y := by
  have hwx := weight_nonneg hx.le
  have hwy := weight_nonneg hy.le
  exact (by positivity : 0 ≤ (weight x + weight y) * (x - y) ^ 2 /
    (24 * x * (x + y))).trans (scalar_remainder_lower hx hy)

lemma scalar_remainder_reverse_lower {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (weight x + weight y) * (x - y) ^ 2 / (24 * x * (x + y)) ≤
      (y / x) * scalarRemainder y x := by
  calc
    _ = (y / x) * ((weight y + weight x) * (y - x) ^ 2 / (24 * y * (y + x))) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (scalar_remainder_lower hy hx) (by positivity)

lemma cutoff_nonneg (x : ℝ) : 0 ≤ cutoff x := by
  unfold cutoff
  split_ifs <;> linarith

lemma cutoff_le_one (x : ℝ) : cutoff x ≤ 1 := by
  unfold cutoff
  split_ifs <;> linarith

lemma cutoff_dist_le_one (x y : ℝ) : |cutoff x - cutoff y| ≤ 1 := by
  have hx := cutoff_nonneg x
  have hy := cutoff_nonneg y
  have hx1 := cutoff_le_one x
  have hy1 := cutoff_le_one y
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma cutoff_dist_of_le {x y : ℝ} (hxy : x ≤ y) :
    |cutoff x - cutoff y| ≤ 2 * (y - x) := by
  apply abs_le.mpr
  unfold cutoff
  split_ifs <;> constructor <;> linarith

lemma cutoff_dist (x y : ℝ) : |cutoff x - cutoff y| ≤ 2 * |x - y| := by
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    exact cutoff_dist_of_le h
  · rw [abs_sub_comm (cutoff x), abs_of_nonneg (sub_nonneg.mpr h)]
    exact cutoff_dist_of_le h

lemma cutoff_zero_of_not_band {x : ℝ} (h : ¬ (1 / 2 ≤ x ∧ x ≤ 4)) : cutoff x = 0 := by
  unfold cutoff
  split_ifs <;> first | rfl | (exfalso; apply h; constructor <;> linarith)

lemma cutoff_ne_band {x y : ℝ} (h : cutoff x ≠ cutoff y) :
    (1 / 2 ≤ x ∧ x ≤ 4) ∨ (1 / 2 ≤ y ∧ y ≤ 4) := by
  by_contra hn
  have hn := not_or.mp hn
  exact h (by rw [cutoff_zero_of_not_band hn.1, cutoff_zero_of_not_band hn.2])

lemma weight_band {x : ℝ} (hx : 1 / 2 ≤ x ∧ x ≤ 4) : 1 / 4 ≤ weight x := by
  apply le_min
  · calc
      1 / 4 = (1 / 2 : ℝ) ^ (2 : ℝ) := by norm_num
      _ ≤ (1 / 2 : ℝ) ^ exponent :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num [exponent])
      _ ≤ x ^ exponent := Real.rpow_le_rpow (by norm_num) hx.1 exponent_pos.le
  · simpa only [one_div] using one_div_le_one_div_of_le (by linarith : 0 < x) hx.2

private lemma cutoff_weighted_distance {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hb : x ≤ 4 ∨ y ≤ 4) :
    (1 + y) * (cutoff x - cutoff y) ^ 2 * x * (x + y) ≤ 1200 * (x - y) ^ 2 := by
  let z := |x - y|
  have hz : 0 ≤ z := abs_nonneg _
  have hzx : x ≤ y + z := by have := le_abs_self (x - y); dsimp only [z]; linarith
  have hzy : y ≤ x + z := by have := neg_le_abs (x - y); dsimp only [z]; linarith
  have hsqz : z ^ 2 = (x - y) ^ 2 := sq_abs _
  have hd : (cutoff x - cutoff y) ^ 2 ≤ 4 * z ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (cutoff x - cutoff y)) (by positivity : 0 ≤ 2 * z)).mpr
      (cutoff_dist x y)
    simpa only [sq_abs, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using h
  have hd1 : (cutoff x - cutoff y) ^ 2 ≤ 1 := by
    have h := (sq_le_sq₀ (abs_nonneg (cutoff x - cutoff y)) (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (cutoff_dist_le_one x y)
    simpa only [sq_abs, one_pow] using h
  have ha : 0 ≤ (1 + y) * x * (x + y) := by positivity
  by_cases hz1 : z ≤ 1
  · have hx5 : x ≤ 5 := by rcases hb with h | h <;> linarith
    have hy5 : y ≤ 5 := by rcases hb with h | h <;> linarith
    have ha300 : (1 + y) * x * (x + y) ≤ 300 := by
      calc
        _ ≤ (6 * 5) * 10 := mul_le_mul
          (mul_le_mul (by linarith : 1 + y ≤ 6) hx5 hx.le (by norm_num))
          (by linarith) (by positivity) (by norm_num)
        _ = _ := by norm_num
    have h := mul_le_mul ha300 hd (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 300)
    nlinarith only [h, hsqz]
  · have hz1 : 1 ≤ z := le_of_not_ge hz1
    have ha1200 : (1 + y) * x * (x + y) ≤ 1200 * z ^ 2 := by
      rcases hb with hb | hb
      · have hy5 : y ≤ 5 * z := by linarith
        have h := mul_le_mul
          (mul_le_mul (by linarith : 1 + y ≤ 6 * z) hb hx.le (by positivity))
          (by linarith : x + y ≤ 9 * z) (by positivity) (by positivity : 0 ≤ 6 * z * 4)
        nlinarith only [h, sq_nonneg z]
      · have hx5 : x ≤ 5 * z := by linarith
        have h := mul_le_mul
          (mul_le_mul (by linarith : 1 + y ≤ 5) hx5 hx.le (by norm_num))
          (by linarith : x + y ≤ 9 * z) (by positivity) (by positivity : 0 ≤ 5 * (5 * z))
        nlinarith only [h, sq_nonneg z]
    have h := mul_le_mul ha1200 hd1 (sq_nonneg _) (by positivity : 0 ≤ 1200 * z ^ 2)
    nlinarith only [h, hsqz]

lemma scalar_comparison {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (1 / 115200) * (1 + y) * |cutoff x - cutoff y| ^ 2 ≤ scalarRemainder x y ∧
    (1 / 115200) * (1 + y) * |cutoff x - cutoff y| ^ 2 ≤ (y / x) * scalarRemainder y x := by
  by_cases hf : cutoff x = cutoff y
  · simp only [hf, sub_self, abs_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
    exact ⟨scalar_remainder_nonneg hx hy,
      mul_nonneg (by positivity) (scalar_remainder_nonneg hy hx)⟩
  have hb := cutoff_ne_band hf
  have hw : 1 / 4 ≤ weight x + weight y := by
    have hwx := weight_nonneg hx.le
    have hwy := weight_nonneg hy.le
    rcases hb with hb | hb
    · have := weight_band hb
      linarith
    · have := weight_band hb
      linarith
  have hd := cutoff_weighted_distance hx hy (hb.imp And.right And.right)
  have ht : (1 / 115200) * (1 + y) * |cutoff x - cutoff y| ^ 2 ≤
      (weight x + weight y) * (x - y) ^ 2 / (24 * x * (x + y)) := by
    apply (le_div_iff₀ (by positivity : 0 < 24 * x * (x + y))).mpr
    rw [sq_abs]
    have h := mul_le_mul_of_nonneg_right hw (sq_nonneg (x - y))
    nlinarith only [hd, h]
  exact ⟨ht.trans (scalar_remainder_lower hx hy), ht.trans (scalar_remainder_reverse_lower hx hy)⟩

lemma cutoff_square_le_weight {x : ℝ} (hx : 0 < x) : cutoff x ^ 2 ≤ 4 * weight x := by
  by_cases h : cutoff x = 0
  · rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact mul_nonneg (by norm_num) (weight_nonneg hx.le)
  have hb : 1 / 2 ≤ x ∧ x ≤ 4 := by
    by_contra hn
    exact h (cutoff_zero_of_not_band hn)
  have hw := weight_band hb
  have hf0 := cutoff_nonneg x
  have hf1 := cutoff_le_one x
  nlinarith

lemma cutoff_weighted_square_le_weight {x : ℝ} (hx : 0 < x) :
    (1 + x) * cutoff x ^ 2 ≤ 20 * weight x := by
  by_cases h : cutoff x = 0
  · rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
    exact mul_nonneg (by norm_num) (weight_nonneg hx.le)
  have hb : 1 / 2 ≤ x ∧ x ≤ 4 := by
    by_contra hn
    exact h (cutoff_zero_of_not_band hn)
  have hw := weight_band hb
  have hf0 := cutoff_nonneg x
  have hf1 := cutoff_le_one x
  have hf2 : cutoff x ^ 2 ≤ 1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hf2 (by positivity : 0 ≤ 1 + x)
  nlinarith

lemma cutoff_scaled_square_le_weight {x : ℝ} (hx : 0 < x) :
    x * cutoff x ^ 2 ≤ 16 * weight x := by
  by_cases h : cutoff x = 0
  · rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
    exact mul_nonneg (by norm_num) (weight_nonneg hx.le)
  have hb : 1 / 2 ≤ x ∧ x ≤ 4 := by
    by_contra hn
    exact h (cutoff_zero_of_not_band hn)
  have hw := weight_band hb
  have hf0 := cutoff_nonneg x
  have hf1 := cutoff_le_one x
  have hf2 : cutoff x ^ 2 ≤ 1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hf2 hx.le
  nlinarith

end Scalar

section SpectralEndpoints

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private lemma sum_row (m : ι → κ → ℝ) (f : ι → ℝ) :
    (∑ i, ∑ j, m i j * f i) = ∑ i, (∑ j, m i j) * f i := by
  simp_rw [Finset.sum_mul]

private lemma sum_col (m : ι → κ → ℝ) (f : κ → ℝ) :
    (∑ i, ∑ j, m i j * f j) = ∑ j, (∑ i, m i j) * f j := by
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]

lemma contraction_deficit_identity
    (x : ι → ℝ) (y : κ → ℝ) (m n : ι → κ → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 < y j)
    (hn : ∀ i j, n i j = m i j * y j / x i)
    (hrow : ∀ i, ∑ j, n i j = 1) (hcol : ∀ j, ∑ i, n i j = 1) :
    (∑ j, potential (y j)) - (∑ i, potential (x i)) =
      (∑ i, ∑ j, n i j * scalarRemainder (y j) (x i)) +
      (∑ i, (1 - ∑ j, m i j) * weight (x i)) / 2 +
      (∑ j, (1 - ∑ i, m i j) * weight (y j)) / 2 := by
  have hp (i : ι) (j : κ) :
      n i j * scalarRemainder (y j) (x i) =
        n i j * potential (y j) - n i j * potential (x i) +
        (m i j * weight (x i) - n i j * weight (x i)) / 2 +
        (m i j * weight (y j) - n i j * weight (y j)) / 2 := by
    rw [hn]
    dsimp only [scalarRemainder]
    field_simp [ne_of_gt (hx i), ne_of_gt (hy j)]
    ring
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib]
  rw [sum_col n, sum_row n, sum_row m, sum_row n, sum_col m, sum_col n]
  simp_rw [hrow, hcol, one_mul, sub_mul, one_mul, Finset.sum_sub_distrib]
  ring

lemma contraction_spectral_bound
    (x : ι → ℝ) (y : κ → ℝ) (m n : ι → κ → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 < y j)
    (hm : ∀ i j, 0 ≤ m i j)
    (hmrow : ∀ i, ∑ j, m i j ≤ 1) (hmcol : ∀ j, ∑ i, m i j ≤ 1)
    (hn : ∀ i j, n i j = m i j * y j / x i)
    (hrow : ∀ i, ∑ j, n i j = 1) (hcol : ∀ j, ∑ i, n i j = 1) :
    (∑ i, ∑ j, m i j * (1 + y j) * (cutoff (x i) - cutoff (y j)) ^ 2) +
      (∑ i, (1 - ∑ j, m i j) * cutoff (x i) ^ 2) +
      (∑ j, (1 - ∑ i, m i j) * (1 + y j) * cutoff (y j) ^ 2) ≤
        115200 * ((∑ j, potential (y j)) - (∑ i, potential (x i))) := by
  have hp (i : ι) (j : κ) :
      m i j * (1 + y j) * (cutoff (x i) - cutoff (y j)) ^ 2 ≤
        115200 * (n i j * scalarRemainder (y j) (x i)) := by
    have h := mul_le_mul_of_nonneg_left (scalar_comparison (hx i) (hy j)).2 (hm i j)
    rw [sq_abs] at h
    rw [hn]
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith only [h]
  have hd (i : ι) : (1 - ∑ j, m i j) * cutoff (x i) ^ 2 ≤
      57600 * ((1 - ∑ j, m i j) * weight (x i)) := by
    have h := mul_le_mul_of_nonneg_left (cutoff_square_le_weight (hx i))
      (sub_nonneg.mpr (hmrow i))
    have hnn := mul_nonneg (sub_nonneg.mpr (hmrow i)) (weight_nonneg (hx i).le)
    nlinarith only [h, hnn]
  have he (j : κ) : (1 - ∑ i, m i j) * (1 + y j) * cutoff (y j) ^ 2 ≤
      57600 * ((1 - ∑ i, m i j) * weight (y j)) := by
    have h := mul_le_mul_of_nonneg_left (cutoff_weighted_square_le_weight (hy j))
      (sub_nonneg.mpr (hmcol j))
    have hnn := mul_nonneg (sub_nonneg.mpr (hmcol j)) (weight_nonneg (hy j).le)
    nlinarith only [h, hnn]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  have hd := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hd i)
  have he := Finset.sum_le_sum (s := Finset.univ) (fun j _ => he j)
  simp_rw [← Finset.mul_sum] at hs hd he
  rw [contraction_deficit_identity x y m n hx hy hn hrow hcol]
  linarith only [hs, hd, he]

lemma gain_deficit_identity
    (x : ι → ℝ) (y : κ → ℝ) (m n : ι → κ → ℝ)
    (hx : ∀ i, 0 < x i)
    (hn : ∀ i j, n i j = m i j * y j / x i)
    (hrow : ∀ i, ∑ j, m i j = 1) (hcol : ∀ j, ∑ i, m i j = 1) :
    (∑ i, potential (x i)) - (∑ j, potential (y j)) =
      (∑ i, ∑ j, m i j * scalarRemainder (x i) (y j)) +
      (∑ i, (1 - ∑ j, n i j) * weight (x i)) / 2 +
      (∑ j, (1 - ∑ i, n i j) * weight (y j)) / 2 := by
  have hp (i : ι) (j : κ) :
      m i j * scalarRemainder (x i) (y j) =
        m i j * potential (x i) - m i j * potential (y j) +
        (n i j * weight (x i) - m i j * weight (x i)) / 2 +
        (n i j * weight (y j) - m i j * weight (y j)) / 2 := by
    rw [hn]
    dsimp only [scalarRemainder]
    field_simp [ne_of_gt (hx i)]
    ring
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib]
  rw [sum_row m, sum_col m, sum_row n, sum_row m, sum_col n, sum_col m]
  simp_rw [hrow, hcol, one_mul, sub_mul, one_mul, Finset.sum_sub_distrib]
  ring

lemma gain_spectral_bound
    (x : ι → ℝ) (y : κ → ℝ) (m n : ι → κ → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 < y j)
    (hm : ∀ i j, 0 ≤ m i j)
    (hrow : ∀ i, ∑ j, m i j = 1) (hcol : ∀ j, ∑ i, m i j = 1)
    (hn : ∀ i j, n i j = m i j * y j / x i)
    (hnrow : ∀ i, ∑ j, n i j ≤ 1) (hncol : ∀ j, ∑ i, n i j ≤ 1) :
    (∑ i, ∑ j, m i j * (1 + y j) * (cutoff (x i) - cutoff (y j)) ^ 2) +
      (∑ i, x i * (1 - ∑ j, n i j) * cutoff (x i) ^ 2) ≤
        115200 * ((∑ i, potential (x i)) - (∑ j, potential (y j))) := by
  have hp (i : ι) (j : κ) :
      m i j * (1 + y j) * (cutoff (x i) - cutoff (y j)) ^ 2 ≤
        115200 * (m i j * scalarRemainder (x i) (y j)) := by
    have h := mul_le_mul_of_nonneg_left (scalar_comparison (hx i) (hy j)).1 (hm i j)
    rw [sq_abs] at h
    nlinarith only [h]
  have hd (i : ι) : x i * (1 - ∑ j, n i j) * cutoff (x i) ^ 2 ≤
      57600 * ((1 - ∑ j, n i j) * weight (x i)) := by
    have h := mul_le_mul_of_nonneg_left (cutoff_scaled_square_le_weight (hx i))
      (sub_nonneg.mpr (hnrow i))
    have hnn := mul_nonneg (sub_nonneg.mpr (hnrow i)) (weight_nonneg (hx i).le)
    nlinarith only [h, hnn]
  have he : 0 ≤ ∑ j, (1 - ∑ i, n i j) * weight (y j) :=
    Finset.sum_nonneg (fun j _ =>
      mul_nonneg (sub_nonneg.mpr (hncol j)) (weight_nonneg (hy j).le))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  have hd := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hd i)
  simp_rw [← Finset.mul_sum] at hs hd
  rw [gain_deficit_identity x y m n hx hn hrow hcol]
  linarith only [hs, hd, he]

end SpectralEndpoints

section RealMatrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def hsSquared {κ : Type*} [Fintype κ] (A : Matrix ι κ ℝ) : ℝ :=
  (A * A.transpose).trace

omit [DecidableEq ι] in
lemma hermitian_dot (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (x y : ι → ℝ) : x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
  have ht : A.transpose = A := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  have hx : x ᵥ* A = A *ᵥ x := by simpa only [ht] using Matrix.vecMul_transpose A x
  rw [Matrix.dotProduct_mulVec, hx]

lemma le_of_square_le {S T : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hT : T.PosSemidef) (hst : S * S ≤ T * T) : S ≤ T := by
  let D := T - S
  have hD : D.IsHermitian := hT.1.sub hS.1
  change D.PosSemidef
  apply hD.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  let v : ι → ℝ := (hD.eigenvectorBasis i).ofLp
  let eig := hD.eigenvalues i
  have heig : D *ᵥ v = eig • v := hD.mulVec_eigenvectorBasis i
  have hv : v ⬝ᵥ v = 1 := by
    have hn := real_inner_self_eq_norm_sq (hD.eigenvectorBasis i)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      OrthonormalBasis.norm_eq_one, one_pow] using hn
  have hs : 0 ≤ v ⬝ᵥ (S *ᵥ v) := by
    simpa only [star_trivial] using hS.dotProduct_mulVec_nonneg v
  have ht : 0 ≤ v ⬝ᵥ (T *ᵥ v) := by
    simpa only [star_trivial] using hT.dotProduct_mulVec_nonneg v
  have hd : v ⬝ᵥ (T *ᵥ v) - v ⬝ᵥ (S *ᵥ v) = eig := by
    have hdv : v ⬝ᵥ (D *ᵥ v) = eig := by rw [heig, dotProduct_smul, hv]; simp
    simpa only [D, Matrix.sub_mulVec, dotProduct_sub] using hdv
  have hq : 0 ≤ v ⬝ᵥ ((T * T - S * S) *ᵥ v) := by
    simpa only [star_trivial] using (Matrix.le_iff.mp hst).dotProduct_mulVec_nonneg v
  have hid : T * T - S * S = T * D + D * S := by dsimp [D]; noncomm_ring
  have hformula : v ⬝ᵥ ((T * T - S * S) *ᵥ v) =
      eig * (v ⬝ᵥ (T *ᵥ v) + v ⬝ᵥ (S *ᵥ v)) := by
    rw [hid, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, dotProduct_smul,
      hermitian_dot D hD, heig, smul_dotProduct]
    simp only [smul_eq_mul]
    ring
  rw [hformula] at hq
  change 0 ≤ eig
  by_contra hh
  have hn : eig < 0 := lt_of_not_ge hh
  have hp : 0 < v ⬝ᵥ (T *ᵥ v) + v ⬝ᵥ (S *ᵥ v) := by linarith
  exact (not_lt_of_ge hq) (mul_neg_of_neg_of_pos hn hp)

lemma sqrt_le_sqrt {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hab : A ≤ B) : CFC.sqrt A ≤ CFC.sqrt B := by
  apply le_of_square_le (CFC.sqrt_nonneg A).posSemidef (CFC.sqrt_nonneg B).posSemidef
  simpa only [← sq, CFC.sq_sqrt A hA.nonneg, CFC.sq_sqrt B hB.nonneg] using hab

lemma inv_le_inv {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (hab : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  let _ := hA.isUnit.invertible
  let _ := hB.isUnit.invertible
  have hD : (A⁻¹ - B⁻¹).IsHermitian := hA.1.inv.sub hB.1.inv
  have h₁ := hA.posSemidef.conjTranspose_mul_mul_same (A⁻¹ - B⁻¹)
  rw [hD.eq] at h₁
  have h₂ := (Matrix.le_iff.mp hab).conjTranspose_mul_mul_same B⁻¹
  rw [hB.1.inv.eq] at h₂
  have hid : (A⁻¹ - B⁻¹) * A * (A⁻¹ - B⁻¹) + B⁻¹ * (B - A) * B⁻¹ =
      A⁻¹ - B⁻¹ := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
      Matrix.mul_inv_of_invertible, Matrix.inv_mul_of_invertible,
      Matrix.mul_one, Matrix.one_mul]
    abel
  exact Matrix.le_iff.mpr (hid ▸ h₁.add h₂)

lemma trace_mul_nonneg {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  have hS : (CFC.sqrt A).IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
  have h := hB.conjTranspose_mul_mul_same (CFC.sqrt A)
  rw [hS.eq] at h
  have ht := h.trace_nonneg
  rw [Matrix.trace_mul_cycle, ← sq, CFC.sq_sqrt A hA.nonneg] at ht
  exact ht

lemma trace_mul_mono_right {A B Q : Matrix ι ι ℝ}
    (hab : A ≤ B) (hQ : Q.PosSemidef) : (A * Q).trace ≤ (B * Q).trace := by
  have h := trace_mul_nonneg (Matrix.le_iff.mp hab) hQ
  simpa only [Matrix.sub_mul, Matrix.trace_sub, sub_nonneg] using h

end RealMatrices
end EuclideanSteinitz.MatrixEnergy

end OAI
