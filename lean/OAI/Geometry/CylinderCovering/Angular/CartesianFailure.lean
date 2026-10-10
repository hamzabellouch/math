import Mathlib

namespace OAI

namespace AngularCartesianValidation

theorem cartesian_failure_displacement
    {x y s τ η : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hη : 0 ≤ η)
    (hfirst : 1 / 4 + τ * x * y +
      τ ^ 2 * ((y ^ 2 / 4 + y ^ 4) + η / 2 - x ^ 2 / 4) < s ^ 2)
    (hsecond : 1 / 4 - τ * x * y +
      τ ^ 2 * ((x ^ 2 / 4 + x ^ 4) + η / 2 - y ^ 2 / 4) < (1 - s) ^ 2) :
    |s - 1 / 2| ≤ 3 * τ ∧ |s - 1 / 2 - τ * x * y| ≤ 10 * τ ^ 2 := by
  let u := s - 1 / 2
  have hu0 : -(1 / 2 : ℝ) ≤ u := by dsimp [u]; linarith
  have hu1 : u ≤ (1 / 2 : ℝ) := by dsimp [u]; linarith
  have hx2 : x ^ 2 ≤ 1 := by
    nlinarith only [(abs_le.mp hx).1, (abs_le.mp hx).2]
  have hy2 : y ^ 2 ≤ 1 := by
    nlinarith only [(abs_le.mp hy).1, (abs_le.mp hy).2]
  have hxy : |x * y| ≤ 1 := by
    rw [abs_mul]
    nlinarith only [mul_le_mul hx hy (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1)]
  have htxyl : -τ ≤ τ * x * y := by
    nlinarith only [mul_le_mul_of_nonneg_left (abs_le.mp hxy).1 hτ.le]
  have htxyr : τ * x * y ≤ τ := by
    nlinarith only [mul_le_mul_of_nonneg_left (abs_le.mp hxy).2 hτ.le]
  have hτsq : τ ^ 2 ≤ τ := by
    nlinarith only [mul_nonneg hτ.le (sub_nonneg.mpr hτ1)]
  have hA : -(1 / 4 : ℝ) ≤ (y ^ 2 / 4 + y ^ 4) + η / 2 - x ^ 2 / 4 := by
    nlinarith only [sq_nonneg y, sq_nonneg (y ^ 2), hx2, hη]
  have hB : -(1 / 4 : ℝ) ≤ (x ^ 2 / 4 + x ^ 4) + η / 2 - y ^ 2 / 4 := by
    nlinarith only [sq_nonneg x, sq_nonneg (x ^ 2), hy2, hη]
  have hfirst' : τ * x * y - τ ^ 2 / 4 < u + u ^ 2 := by
    dsimp [u]
    nlinarith only [hfirst, mul_le_mul_of_nonneg_left hA (sq_nonneg τ)]
  have hsecond' : -τ * x * y - τ ^ 2 / 4 < -u + u ^ 2 := by
    dsimp [u]
    nlinarith only [hsecond, mul_le_mul_of_nonneg_left hB (sq_nonneg τ)]
  have hul : -3 * τ ≤ u := by
    by_cases hu : 0 ≤ u
    · linarith
    · have hmul := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hu)
        (show 0 ≤ u + 1 / 2 by linarith)
      nlinarith only [hmul, hfirst', htxyl, hτsq, hτ.le]
  have hur : u ≤ 3 * τ := by
    by_cases hu : u ≤ 0
    · linarith
    · have hmul := mul_nonpos_of_nonneg_of_nonpos (le_of_not_ge hu)
        (show u - 1 / 2 ≤ 0 by linarith)
      nlinarith only [hmul, hsecond', htxyr, hτsq, hτ.le]
  have hu2 : u ^ 2 ≤ 9 * τ ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hur)
      (show 0 ≤ u + 3 * τ by linarith only [hul])]
  constructor
  · exact abs_le.mpr ⟨by simpa only [neg_mul] using hul, hur⟩
  · change |u - τ * x * y| ≤ 10 * τ ^ 2
    apply abs_le.mpr
    constructor
    · nlinarith only [hfirst', hu2, sq_nonneg τ]
    · nlinarith only [hsecond', hu2, sq_nonneg τ]

theorem cartesian_squared_failures_impossible
    {x y s τ η : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hη : 0 < η) (hsmall : τ ≤ η / 80)
    (hfirst : 1 / 4 + τ * x * y +
      τ ^ 2 * ((y ^ 2 / 4 + y ^ 4) + η / 2 - x ^ 2 / 4) < s ^ 2)
    (hsecond : 1 / 4 - τ * x * y +
      τ ^ 2 * ((x ^ 2 / 4 + x ^ 4) + η / 2 - y ^ 2 / 4) < (1 - s) ^ 2) :
    False := by
  obtain ⟨hu, herr⟩ := cartesian_failure_displacement hx hy hs0 hs1 hτ hτ1 hη.le
    hfirst hsecond
  let u := s - 1 / 2
  change |u| ≤ 3 * τ at hu
  change |u - τ * x * y| ≤ 10 * τ ^ 2 at herr
  have hxy : |x * y| ≤ 1 := by
    rw [abs_mul]
    nlinarith only [mul_le_mul hx hy (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1)]
  have htx : |τ * x * y| ≤ τ := by
    calc
      |τ * x * y| = τ * |x * y| := by rw [mul_assoc, abs_mul, abs_of_pos hτ]
      _ ≤ τ * 1 := mul_le_mul_of_nonneg_left hxy hτ.le
      _ = τ := mul_one τ
  have hsum : |u + τ * x * y| ≤ 4 * τ := by
    exact (abs_add_le _ _).trans (by linarith)
  have hsq : |u ^ 2 - (τ * x * y) ^ 2| ≤ 40 * τ ^ 3 := by
    calc
      |u ^ 2 - (τ * x * y) ^ 2| = |u - τ * x * y| * |u + τ * x * y| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ (10 * τ ^ 2) * (4 * τ) :=
        mul_le_mul herr hsum (abs_nonneg _) (by positivity)
      _ = 40 * τ ^ 3 := by ring
  have hsumfail : τ ^ 2 * (x ^ 4 + y ^ 4 + η) < 2 * u ^ 2 := by
    dsimp [u]
    nlinarith only [hfirst, hsecond]
  have hquartic : 2 * x ^ 2 * y ^ 2 ≤ x ^ 4 + y ^ 4 := by
    nlinarith only [sq_nonneg (x ^ 2 - y ^ 2)]
  have hgap : η * τ ^ 2 < 2 * (u ^ 2 - (τ * x * y) ^ 2) := by
    nlinarith only [hsumfail, mul_le_mul_of_nonneg_left hquartic (sq_nonneg τ)]
  have hwindow : 80 * τ ^ 3 ≤ η * τ ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hsmall (sq_nonneg τ)]
  nlinarith only [hgap, hwindow, (abs_le.mp hsq).2]

theorem cartesian_squared_lower_of_sqrt {Q τ c : ℝ} (hc : 0 ≤ c)
    (hroot : 1 / 2 + τ ^ 2 * c < Real.sqrt Q) :
    1 / 4 + τ ^ 2 * c < Q := by
  have hbase : 0 < 1 / 2 + τ ^ 2 * c := by positivity
  have hQ : 0 ≤ Q := (Real.sqrt_pos.mp (hbase.trans hroot)).le
  have hsq := mul_self_lt_mul_self hbase.le hroot
  rw [Real.mul_self_sqrt hQ] at hsq
  nlinarith only [hsq, sq_nonneg (τ ^ 2 * c)]

theorem cartesian_sqrt_failures_impossible
    {x y s τ η : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hη : 0 < η) (hsmall : τ ≤ η / 80)
    (hfirst : 1 / 2 + τ ^ 2 * ((y ^ 2 / 4 + y ^ 4) + η / 2) <
      Real.sqrt (s ^ 2 - τ * x * y + τ ^ 2 * x ^ 2 / 4))
    (hsecond : 1 / 2 + τ ^ 2 * ((x ^ 2 / 4 + x ^ 4) + η / 2) <
      Real.sqrt ((1 - s) ^ 2 + τ * x * y + τ ^ 2 * y ^ 2 / 4)) :
    False := by
  have hfirst' := cartesian_squared_lower_of_sqrt (by positivity) hfirst
  have hsecond' := cartesian_squared_lower_of_sqrt (by positivity) hsecond
  apply cartesian_squared_failures_impossible hx hy hs0 hs1 hτ hτ1 hη hsmall
  · nlinarith only [hfirst']
  · nlinarith only [hsecond']

theorem cartesian_edge_one_obstruction (ε x y : ℝ) :
    (ε / 2) ^ 2 * (((2 * x) ^ 2 - (2 * y) ^ 2) ^ 2 + 1 / 1000) =
      ε ^ 2 * (4 * (x ^ 2 - y ^ 2) ^ 2 + 1 / 4000) := by
  ring

end AngularCartesianValidation

end OAI
