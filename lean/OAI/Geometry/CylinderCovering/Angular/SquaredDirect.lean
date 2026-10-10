import OAI.Geometry.CylinderCovering.Angular.Estimates
import OAI.Geometry.CylinderCovering.Angular.SquaredDirectDefinitions

namespace OAI

namespace AngularEstimates

theorem selected_square_remainder_identity
    {k x q M B s S y : ℝ}
    (hsec : 2 * B - M ^ 2 = 1 - k ^ 4)
    (hS : S = s - k * x * M) (hy : y = q * S + k * x * B) :
    S ^ 2 - (s ^ 2 - 2 * k * x * y + k ^ 2 * x ^ 2) =
      2 * k * x * S * (q - M) - k ^ 6 * x ^ 2 := by
  calc
    S ^ 2 - (s ^ 2 - 2 * k * x * y + k ^ 2 * x ^ 2) =
        2 * k * x * S * (q - M) + k ^ 2 * x ^ 2 * (2 * B - M ^ 2 - 1) := by
          rw [hy, hS]
          ring
    _ = 2 * k * x * S * (q - M) - k ^ 6 * x ^ 2 := by
      rw [show 2 * B - M ^ 2 - 1 = -(k ^ 4) by linarith only [hsec]]
      ring

theorem selected_square_remainder_bound
    {k x q M B s S y : ℝ}
    (hk : 0 ≤ k) (hk1 : k ≤ 1) (hx : |x| ≤ 1) (hS2 : |S| ≤ 2)
    (hqM : |q - M| ≤ k ^ 2)
    (hsec : 2 * B - M ^ 2 = 1 - k ^ 4)
    (hS : S = s - k * x * M) (hy : y = q * S + k * x * B) :
    |S ^ 2 - (s ^ 2 - 2 * k * x * y + k ^ 2 * x ^ 2)| ≤ 5 * k ^ 3 := by
  rw [selected_square_remainder_identity hsec hS hy]
  have hfirst : |2 * k * x * S * (q - M)| ≤ 4 * k ^ 3 := by
    calc
      |2 * k * x * S * (q - M)| = 2 * k * |x| * |S| * |q - M| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hk]
        norm_num
      _ ≤ 2 * k * 1 * 2 * k ^ 2 := by gcongr
      _ = 4 * k ^ 3 := by ring
  have hx2 : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hx
  have hk3 : k ^ 3 ≤ 1 := pow_le_one₀ hk hk1
  have hk63 : k ^ 6 ≤ k ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_left hk3 (pow_nonneg hk 3)]
  have hsecond : |k ^ 6 * x ^ 2| ≤ k ^ 3 := by
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg hk 6) (sq_nonneg x))]
    exact (mul_le_of_le_one_right (pow_nonneg hk 6) hx2).trans hk63
  exact (abs_sub _ _).trans (by linarith)

theorem squared_profile_replacement
    {k q y : ℝ} (hk : 0 ≤ k) (hq : |q| ≤ 1) (hy : |y| ≤ 1)
    (hclose : |q - 2 * y| ≤ 6 * k) :
    |(q ^ 2 + q ^ 4) / 4 - (y ^ 2 + 4 * y ^ 4)| ≤ 27 * k := by
  have hsum : |q + 2 * y| ≤ 3 := by
    calc
      |q + 2 * y| ≤ |q| + |2 * y| := abs_add_le _ _
      _ = |q| + 2 * |y| := by rw [abs_mul]; norm_num
      _ ≤ 3 := by linarith
  have hdiff2 : |q ^ 2 - 4 * y ^ 2| ≤ 18 * k := by
    calc
      |q ^ 2 - 4 * y ^ 2| = |q - 2 * y| * |q + 2 * y| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ (6 * k) * 3 := mul_le_mul hclose hsum (abs_nonneg _) (by positivity)
      _ = 18 * k := by ring
  have hq2 : q ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one q).2 hq
  have hy2 : y ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one y).2 hy
  have hsum2 : |q ^ 2 + 4 * y ^ 2| ≤ 5 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hdiff4 : |q ^ 4 - 16 * y ^ 4| ≤ 90 * k := by
    calc
      |q ^ 4 - 16 * y ^ 4| = |q ^ 2 - 4 * y ^ 2| * |q ^ 2 + 4 * y ^ 2| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ (18 * k) * 5 := mul_le_mul hdiff2 hsum2 (abs_nonneg _) (by positivity)
      _ = 90 * k := by ring
  calc
    |(q ^ 2 + q ^ 4) / 4 - (y ^ 2 + 4 * y ^ 4)| =
        |(q ^ 2 - 4 * y ^ 2) + (q ^ 4 - 16 * y ^ 4)| / 4 := by
      have heq : (q ^ 2 + q ^ 4) / 4 - (y ^ 2 + 4 * y ^ 4) =
          ((q ^ 2 - 4 * y ^ 2) + (q ^ 4 - 16 * y ^ 4)) / 4 := by ring
      rw [heq, abs_div]
      norm_num
    _ ≤ (|q ^ 2 - 4 * y ^ 2| + |q ^ 4 - 16 * y ^ 4|) / 4 := by
      gcongr
      exact abs_add_le _ _
    _ ≤ 27 * k := by linarith

theorem squared_failure_balance
    {k x y u S T : ℝ} (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hu : |u| ≤ k)
    (hfirst : |S ^ 2 - (1 / 4 + u + u ^ 2 - 2 * k * x * y + k ^ 2 * x ^ 2)|
      ≤ 5 * k ^ 3)
    (hsecond : |T ^ 2 - (1 / 4 - u + u ^ 2 + 2 * k * x * y + k ^ 2 * y ^ 2)|
      ≤ 5 * k ^ 3)
    (hS : 1 / 4 < S ^ 2) (hT : 1 / 4 < T ^ 2) :
    |u - 2 * k * x * y| ≤ 7 * k ^ 2 := by
  have hu2 : u ^ 2 ≤ k ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg u) hk).2 hu
  have hx2 : k ^ 2 * x ^ 2 ≤ k ^ 2 :=
    mul_le_of_le_one_right (sq_nonneg k) ((sq_le_one_iff_abs_le_one x).2 hx)
  have hy2 : k ^ 2 * y ^ 2 ≤ k ^ 2 :=
    mul_le_of_le_one_right (sq_nonneg k) ((sq_le_one_iff_abs_le_one y).2 hy)
  have hk32 : k ^ 3 ≤ k ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hk1 (sq_nonneg k)]
  rw [abs_le]
  constructor
  · nlinarith only [(abs_le.mp hfirst).2, hS, hu2, hx2, hk32]
  · nlinarith only [(abs_le.mp hsecond).2, hT, hu2, hy2, hk32]

theorem squared_sum_remainder
    {k x y u S T : ℝ} (hk : 0 ≤ k)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hu : |u| ≤ k)
    (hbalance : |u - 2 * k * x * y| ≤ 7 * k ^ 2)
    (hfirst : |S ^ 2 - (1 / 4 + u + u ^ 2 - 2 * k * x * y + k ^ 2 * x ^ 2)|
      ≤ 5 * k ^ 3)
    (hsecond : |T ^ 2 - (1 / 4 - u + u ^ 2 + 2 * k * x * y + k ^ 2 * y ^ 2)|
      ≤ 5 * k ^ 3) :
    |S ^ 2 + T ^ 2 - (1 / 2 + k ^ 2 * (x ^ 2 + y ^ 2 + 8 * x ^ 2 * y ^ 2))|
      ≤ 52 * k ^ 3 := by
  have hsum : |u + 2 * k * x * y| ≤ 3 * k := by
    calc
      |u + 2 * k * x * y| ≤ |u| + |2 * k * x * y| := abs_add_le _ _
      _ = |u| + 2 * k * |x| * |y| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hk]
        norm_num
      _ ≤ k + 2 * k * 1 * 1 := by gcongr
      _ = 3 * k := by ring
  have hsquare : |2 * u ^ 2 - 8 * k ^ 2 * x ^ 2 * y ^ 2| ≤ 42 * k ^ 3 := by
    calc
      |2 * u ^ 2 - 8 * k ^ 2 * x ^ 2 * y ^ 2| =
          2 * |u - 2 * k * x * y| * |u + 2 * k * x * y| := by
        rw [← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← abs_mul, ← abs_mul]
        congr 1
        ring
      _ ≤ 2 * (7 * k ^ 2) * (3 * k) := by gcongr
      _ = 42 * k ^ 3 := by ring
  have heq : S ^ 2 + T ^ 2 - (1 / 2 + k ^ 2 * (x ^ 2 + y ^ 2 + 8 * x ^ 2 * y ^ 2)) =
      (S ^ 2 - (1 / 4 + u + u ^ 2 - 2 * k * x * y + k ^ 2 * x ^ 2)) +
      (T ^ 2 - (1 / 4 - u + u ^ 2 + 2 * k * x * y + k ^ 2 * y ^ 2)) +
      (2 * u ^ 2 - 8 * k ^ 2 * x ^ 2 * y ^ 2) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (by
    have hadd := abs_add_le
      (S ^ 2 - (1 / 4 + u + u ^ 2 - 2 * k * x * y + k ^ 2 * x ^ 2))
      (T ^ 2 - (1 / 4 - u + u ^ 2 + 2 * k * x * y + k ^ 2 * y ^ 2))
    linarith)

theorem selected_slope_replacement
    {k x q M B u S y : ℝ} (hk : 0 ≤ k)
    (hx : |x| ≤ 1) (hq : |q| ≤ 1) (hM : |M| ≤ 1) (hB : |B| ≤ 1)
    (hu : |u| ≤ k)
    (hS : S = 1 / 2 + u - k * x * M) (hy : y = q * S + k * x * B) :
    |q - 2 * y| ≤ 6 * k := by
  have hqMB : |q * M - B| ≤ 2 := by
    calc
      |q * M - B| ≤ |q * M| + |B| := abs_sub _ _
      _ = |q| * |M| + |B| := by rw [abs_mul]
      _ ≤ 1 * 1 + 1 := by gcongr
      _ = 2 := by norm_num
  have hid : q - 2 * y = -2 * (q * u) + 2 * k * x * (q * M - B) := by
    rw [hy, hS]
    ring
  rw [hid]
  calc
    |-2 * (q * u) + 2 * k * x * (q * M - B)| ≤
        |-2 * (q * u)| + |2 * k * x * (q * M - B)| := abs_add_le _ _
    _ = 2 * |q| * |u| + 2 * k * |x| * |q * M - B| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hk]
      norm_num
      ring
    _ ≤ 2 * 1 * k + 2 * k * 1 * 2 := by gcongr
    _ = 6 * k := by ring

theorem squared_sector_data
    {k l r q : ℝ} (hl : -1 ≤ l) (hr : r ≤ 1)
    (hlq : l ≤ q) (hqr : q ≤ r) (hwidth : r - l = 2 * k ^ 2) :
    |(l + r) / 2| ≤ 1 ∧ |(1 + l * r) / 2| ≤ 1 ∧ |q| ≤ 1 ∧
      |q - (l + r) / 2| ≤ k ^ 2 ∧
      2 * ((1 + l * r) / 2) - ((l + r) / 2) ^ 2 = 1 - k ^ 4 := by
  have hlr : l ≤ r := hlq.trans hqr
  have hal : |l| ≤ 1 := abs_le.mpr ⟨hl, hlr.trans hr⟩
  have har : |r| ≤ 1 := abs_le.mpr ⟨hl.trans hlr, hr⟩
  have hprod : |l * r| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hal har (abs_nonneg r) (by norm_num)).trans (by norm_num)
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, ?_,
    abs_le.mpr ⟨hl.trans hlq, hqr.trans hr⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
  · rw [abs_le]
    constructor <;> linarith [(abs_le.mp hprod).1, (abs_le.mp hprod).2]
  · rw [squared_secant_identity, hwidth]
    ring

theorem squared_sum_quotient_remainder
    {k x y S T : ℝ} (hk : 0 < k)
    (herror : |S ^ 2 + T ^ 2 - (1 / 2 + k ^ 2 * (x ^ 2 + y ^ 2 + 8 * x ^ 2 * y ^ 2))|
      ≤ 52 * k ^ 3) :
    |(S ^ 2 + T ^ 2 - 1 / 2) / k ^ 2 - (x ^ 2 + y ^ 2 + 8 * x ^ 2 * y ^ 2)|
      ≤ 52 * k := by
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk
  have hid : (S ^ 2 + T ^ 2 - 1 / 2) / k ^ 2 -
      (x ^ 2 + y ^ 2 + 8 * x ^ 2 * y ^ 2) =
      (S ^ 2 + T ^ 2 - (1 / 2 + k ^ 2 * (x ^ 2 + y ^ 2 + 8 * x ^ 2 * y ^ 2))) /
        k ^ 2 := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_nonneg hk2.le]
  apply (div_le_iff₀ hk2).2
  nlinarith only [herror]

theorem squared_profiles_sum_replacement
    {k x y p q : ℝ} (hk : 0 ≤ k)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (hpclose : |p - 2 * x| ≤ 6 * k) (hqclose : |q - 2 * y| ≤ 6 * k) :
    |(q ^ 2 + q ^ 4) / 4 + (p ^ 2 + p ^ 4) / 4 -
      (x ^ 2 + y ^ 2 + 4 * (x ^ 4 + y ^ 4))| ≤ 54 * k := by
  have hqerror := squared_profile_replacement hk hq hy hqclose
  have hperror := squared_profile_replacement hk hp hx hpclose
  have hid : (q ^ 2 + q ^ 4) / 4 + (p ^ 2 + p ^ 4) / 4 -
      (x ^ 2 + y ^ 2 + 4 * (x ^ 4 + y ^ 4)) =
      ((q ^ 2 + q ^ 4) / 4 - (y ^ 2 + 4 * y ^ 4)) +
      ((p ^ 2 + p ^ 4) / 4 - (x ^ 2 + 4 * x ^ 4)) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith)

theorem selected_sectors_squared_cap
    {k x y s l r l' r' q p S T : ℝ}
    (hk : 0 < k) (hkSmall : k ≤ 1 / 20000)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hl : -1 ≤ l) (hr : r ≤ 1) (hlq : l ≤ q) (hqr : q ≤ r)
    (hwidth : r - l = 2 * k ^ 2)
    (hl' : -1 ≤ l') (hr' : r' ≤ 1) (hlp : l' ≤ p) (hpr : p ≤ r')
    (hwidth' : r' - l' = 2 * k ^ 2)
    (hS0 : 0 ≤ S) (hT0 : 0 ≤ T)
    (hS : S = s - k * x * ((l + r) / 2))
    (hyEq : y = q * S + k * x * ((1 + l * r) / 2))
    (hT : T = 1 - s + k * y * ((l' + r') / 2))
    (hxEq : x = p * T - k * y * ((1 + l' * r') / 2)) :
    S ^ 2 ≤ 1 / 4 + k ^ 2 * ((q ^ 2 + q ^ 4) / 4 + 1 / 240) ∨
      T ^ 2 ≤ 1 / 4 + k ^ 2 * ((p ^ 2 + p ^ 4) / 4 + 1 / 240) := by
  by_contra hfail
  push Not at hfail
  obtain ⟨hM, hB, hq, hqM, hsec⟩ := squared_sector_data hl hr hlq hqr hwidth
  obtain ⟨hN, hC, hp, hpN, hsec'⟩ := squared_sector_data hl' hr' hlp hpr hwidth'
  have hk1 : k ≤ 1 := by linarith only [hkSmall]
  have hprod : |k * x * ((l + r) / 2)| ≤ k := by
    calc
      |k * x * ((l + r) / 2)| = k * |x| * |(l + r) / 2| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hk.le]
      _ ≤ k * 1 * 1 := by gcongr
      _ = k := by ring
  have hprod' : |k * y * ((l' + r') / 2)| ≤ k := by
    calc
      |k * y * ((l' + r') / 2)| = k * |y| * |(l' + r') / 2| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hk.le]
      _ ≤ k * 1 * 1 := by gcongr
      _ = k := by ring
  have hSsq : 1 / 4 < S ^ 2 := by
    have hnonneg : 0 ≤ k ^ 2 * ((q ^ 2 + q ^ 4) / 4 + 1 / 240) := by positivity
    linarith only [hfail.1, hnonneg]
  have hTsq : 1 / 4 < T ^ 2 := by
    have hnonneg : 0 ≤ k ^ 2 * ((p ^ 2 + p ^ 4) / 4 + 1 / 240) := by positivity
    linarith only [hfail.2, hnonneg]
  have hShalf : 1 / 2 < S := by nlinarith only [hS0, hSsq]
  have hThalf : 1 / 2 < T := by nlinarith only [hT0, hTsq]
  have hu : |s - 1 / 2| ≤ k := by
    rw [abs_le]
    constructor
    · linarith only [hShalf, hS, (abs_le.mp hprod).1]
    · linarith only [hThalf, hT, (abs_le.mp hprod').2]
  have hS2 : |S| ≤ 2 := by
    rw [abs_of_nonneg hS0]
    linarith only [hS, hs1, (abs_le.mp hprod).1, hk1]
  have hT2 : |T| ≤ 2 := by
    rw [abs_of_nonneg hT0]
    linarith only [hT, hs0, (abs_le.mp hprod').2, hk1]
  have hfirst : |S ^ 2 - (1 / 4 + (s - 1 / 2) + (s - 1 / 2) ^ 2 -
      2 * k * x * y + k ^ 2 * x ^ 2)| ≤ 5 * k ^ 3 := by
    have h := selected_square_remainder_bound hk.le hk1 hx hS2 hqM hsec hS hyEq
    have hid : s ^ 2 = 1 / 4 + (s - 1 / 2) + (s - 1 / 2) ^ 2 := by ring
    rwa [hid] at h
  have hT' : T = (1 - s) - k * (-y) * ((l' + r') / 2) := by
    nlinarith only [hT]
  have hxEq' : x = p * T + k * (-y) * ((1 + l' * r') / 2) := by
    nlinarith only [hxEq]
  have hny : |-y| ≤ 1 := by simpa only [abs_neg] using hy
  have hsecond : |T ^ 2 - (1 / 4 - (s - 1 / 2) + (s - 1 / 2) ^ 2 +
      2 * k * x * y + k ^ 2 * y ^ 2)| ≤ 5 * k ^ 3 := by
    have h := selected_square_remainder_bound hk.le hk1 hny hT2 hpN hsec' hT' hxEq'
    have hid : (1 - s) ^ 2 - 2 * k * (-y) * x + k ^ 2 * (-y) ^ 2 =
        1 / 4 - (s - 1 / 2) + (s - 1 / 2) ^ 2 + 2 * k * x * y + k ^ 2 * y ^ 2 := by
      ring
    rwa [hid] at h
  have hbalance := squared_failure_balance hk.le hk1 hx hy hu hfirst hsecond hSsq hTsq
  have hsum := squared_sum_remainder hk.le hx hy hu hbalance hfirst hsecond
  have hS' : S = 1 / 2 + (s - 1 / 2) - k * x * ((l + r) / 2) := by
    linarith only [hS]
  have hqclose := selected_slope_replacement hk.le hx hq hM hB hu hS' hyEq
  have hT'' : T = 1 / 2 + (-(s - 1 / 2)) - k * (-y) * ((l' + r') / 2) := by
    nlinarith only [hT]
  have hnu : |-(s - 1 / 2)| ≤ k := by simpa only [abs_neg] using hu
  have hpclose := selected_slope_replacement hk.le hny hp hN hC hnu hT'' hxEq'
  have hqprofile := squared_profile_replacement hk.le hq hy hqclose
  have hpprofile := squared_profile_replacement hk.le hp hx hpclose
  have hprofiles : x ^ 2 + y ^ 2 + 8 * x ^ 2 * y ^ 2 - 54 * k ≤
      (q ^ 2 + q ^ 4) / 4 + (p ^ 2 + p ^ 4) / 4 := by
    linarith only [(abs_le.mp hqprofile).1, (abs_le.mp hpprofile).1,
      squared_radius_obstruction x y]
  have hweighted := mul_le_mul_of_nonneg_left hprofiles (sq_nonneg k)
  have hbad : (1 / 120 : ℝ) * k ^ 2 < 106 * k ^ 3 := by
    nlinarith only [hweighted, hfail.1, hfail.2, (abs_le.mp hsum).2]
  have hsmall : 106 * k < (1 / 120 : ℝ) := by linarith only [hkSmall]
  have hsmallMul := mul_lt_mul_of_pos_right hsmall (sq_pos_of_pos hk)
  nlinarith only [hbad, hsmallMul]

theorem squared_radius_source_formula (k q : ℝ) :
    AngularCaps.squaredRadius (2 * k) (1 / 960) q =
      Real.sqrt (1 / 4 + k ^ 2 * ((q ^ 2 + q ^ 4) / 4 + 1 / 240)) := by
  unfold AngularCaps.squaredRadius AngularCaps.d
  congr 1
  ring

theorem selected_sectors_cap_alternative
    {k x y s l r l' r' q p S T : ℝ}
    (hk : 0 < k) (hkSmall : k ≤ 1 / 20000)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hl : -1 ≤ l) (hr : r ≤ 1) (hlq : l ≤ q) (hqr : q ≤ r)
    (hwidth : r - l = 2 * k ^ 2)
    (hl' : -1 ≤ l') (hr' : r' ≤ 1) (hlp : l' ≤ p) (hpr : p ≤ r')
    (hwidth' : r' - l' = 2 * k ^ 2)
    (hS0 : 0 ≤ S) (hT0 : 0 ≤ T)
    (hS : S = s - k * x * ((l + r) / 2))
    (hyEq : y = q * S + k * x * ((1 + l * r) / 2))
    (hT : T = 1 - s + k * y * ((l' + r') / 2))
    (hxEq : x = p * T - k * y * ((1 + l' * r') / 2)) :
    S ∈ Set.Icc 0 (AngularCaps.squaredRadius (2 * k) (1 / 960) q) ∨
      T ∈ Set.Icc 0 (AngularCaps.squaredRadius (2 * k) (1 / 960) p) := by
  obtain h | h := selected_sectors_squared_cap hk hkSmall hx hy hs0 hs1
    hl hr hlq hqr hwidth hl' hr' hlp hpr hwidth' hS0 hT0 hS hyEq hT hxEq
  · left
    refine ⟨hS0, ?_⟩
    rw [squared_radius_source_formula]
    exact (Real.le_sqrt hS0 (by positivity)).2 h
  · right
    refine ⟨hT0, ?_⟩
    rw [squared_radius_source_formula]
    exact (Real.le_sqrt hT0 (by positivity)).2 h

theorem uniform_squared_direct : SquaredDirectStatement where
  selected_square_remainder_identity := selected_square_remainder_identity
  selected_square_remainder_bound := selected_square_remainder_bound
  squared_profile_replacement := squared_profile_replacement
  squared_failure_balance := squared_failure_balance
  squared_sum_remainder := squared_sum_remainder
  selected_slope_replacement := selected_slope_replacement
  squared_sector_data := squared_sector_data
  squared_sum_quotient_remainder := squared_sum_quotient_remainder
  squared_profiles_sum_replacement := squared_profiles_sum_replacement
  selected_sectors_squared_cap := selected_sectors_squared_cap
  squared_radius_source_formula := squared_radius_source_formula
  selected_sectors_cap_alternative := selected_sectors_cap_alternative

end AngularEstimates

end OAI
