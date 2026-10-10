import OAI.Geometry.CylinderCovering.Rational.RationalThreshold

namespace OAI

namespace CylinderCovering.ThresholdRemainder

theorem inverse_horizontal_expansion
    {e x y Y T a c L : ℝ}
    (he : 0 ≤ e) (he1 : e ≤ 1) (hL : 0 ≤ L) (hx : |x| ≤ 1)
    (ha : |a| ≤ L) (haLip : |a + c| ≤ L * (|Y - y| + |T|))
    (hY : y = Y + e * x * a) (hT : |T| ≤ 3 * L * e ^ 2) :
    |Y - y - e * x * c| ≤ 4 * L ^ 2 * e ^ 2 := by
  have hdis : |Y - y| ≤ e * L := by
    have hid : Y - y = -(e * x * a) := by rw [hY]; ring
    rw [hid, abs_neg, abs_mul, abs_mul, abs_of_nonneg he]
    calc
      e * |x| * |a| ≤ e * 1 * L := by gcongr
      _ = e * L := by ring
  have hid : Y - y - e * x * c = -(e * x * (a + c)) := by rw [hY]; ring
  rw [hid, abs_neg, abs_mul, abs_mul, abs_of_nonneg he]
  calc
    e * |x| * |a + c| ≤ e * 1 * (L * (e * L + 3 * L * e ^ 2)) := by
      gcongr
      exact haLip.trans (mul_le_mul_of_nonneg_left (add_le_add hdis hT) hL)
    _ ≤ 4 * L ^ 2 * e ^ 2 := by
      have hb := mul_le_mul_of_nonneg_right he1
        (show 0 ≤ 3 * L ^ 2 * e ^ 2 by positivity)
      nlinarith only [hb]

theorem inverse_field_expansion
    {e x y Y T α b c L : ℝ}
    (hL : 0 ≤ L) (hα : |α| ≤ 1)
    (hbLip : |b - α * Y| ≤ L * |T|)
    (hT : |T| ≤ 3 * L * e ^ 2)
    (hY : |Y - y - e * x * c| ≤ 4 * L ^ 2 * e ^ 2) :
    |b - α * y - e * α * x * c| ≤ 7 * L ^ 2 * e ^ 2 := by
  have hid : b - α * y - e * α * x * c =
      (b - α * Y) + α * (Y - y - e * x * c) := by ring
  rw [hid]
  calc
    _ ≤ |b - α * Y| + |α * (Y - y - e * x * c)| := abs_add_le _ _
    _ = |b - α * Y| + |α| * |Y - y - e * x * c| := by rw [abs_mul]
    _ ≤ L * (3 * L * e ^ 2) + 1 * (4 * L ^ 2 * e ^ 2) := by
      gcongr
      exact hbLip.trans (mul_le_mul_of_nonneg_left hT hL)
    _ = 7 * L ^ 2 * e ^ 2 := by ring

end CylinderCovering.ThresholdRemainder

namespace SlopeRational.Threshold

theorem threshold_expansions {d : ℝ} (hd : 0 < d) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ e x y Y T : ℝ,
      0 ≤ e → 4 * e * L ≤ 1 → |x| ≤ 1 → |y| ≤ 1 →
      |Y| ≤ 1 → -1 ≤ T → T ≤ 1 / 2 + d / 2 →
      y = Y + e * x * a d Y T →
      T + e * x * b d Y T = e * alpha d * x * y +
        e ^ 2 * (alpha d * x ^ 2 * ceilingCoefficient d y - ceilingPolynomial d y) →
      |T| ≤ 3 * L * e ^ 2 ∧
      |Y - y - e * x * ceilingCoefficient d y| ≤ 4 * L ^ 2 * e ^ 2 ∧
      |b d Y T - alpha d * y - e * alpha d * x * ceilingCoefficient d y| ≤
        7 * L ^ 2 * e ^ 2 ∧
      |T + e ^ 2 * ceilingPolynomial d Y| ≤ 8 * L ^ 2 * e ^ 3 := by
  obtain ⟨L, hL, hreg⟩ := region_estimates hd
  refine ⟨L, hL, ?_⟩
  intro e x y Y T he hsmall hx hy hY hT0 hT1 hyeq hteq
  obtain ⟨ha, hP, haLip, hbLip, hPLip⟩ := hreg Y T y hY hT0 hT1 hy
  have hα : |alpha d| ≤ 1 := by
    unfold alpha
    rw [abs_of_pos (by positivity : 0 < 1 / (1 + 2 * d))]
    exact (div_le_one (by positivity : 0 < 1 + 2 * d)).2 (by linarith)
  obtain ⟨hheight, hceiling⟩ :=
    CylinderCovering.ThresholdRemainder.inverse_threshold_remainder
      he hL hsmall hx hα ha hP haLip hbLip hPLip hyeq hteq
  have hL0 : 0 ≤ L := by linarith
  have he1 : e ≤ 1 := by nlinarith
  have hhorizontal := CylinderCovering.ThresholdRemainder.inverse_horizontal_expansion
    he he1 hL0 hx ha haLip hyeq hheight
  exact ⟨hheight, hhorizontal,
    CylinderCovering.ThresholdRemainder.inverse_field_expansion hL0 hα hbLip hheight hhorizontal,
    hceiling⟩

theorem threshold_inverse_expansions {d : ℝ} (hd : 0 < d) :
    ∃ δ L : ℝ, 0 < δ ∧ 1 ≤ L ∧ ∀ e x y : ℝ,
      0 ≤ e → e < δ → |x| ≤ 1 / 2 → |y| ≤ 1 / 2 →
      ∃! p : Plane, p ∈ inverseRectangle d ∧
        tiltedMap d (e * x) p = vec2 y (threshold d e x y) ∧
        |p 1| ≤ 3 * L * e ^ 2 ∧
        |p 0 - y - e * x * ceilingCoefficient d y| ≤ 4 * L ^ 2 * e ^ 2 ∧
        |b d (p 0) (p 1) - alpha d * y - e * alpha d * x * ceilingCoefficient d y| ≤
          7 * L ^ 2 * e ^ 2 ∧
        |p 1 + e ^ 2 * ceilingPolynomial d (p 0)| ≤ 8 * L ^ 2 * e ^ 3 := by
  obtain ⟨L, hL, hexp⟩ := threshold_expansions hd
  obtain ⟨M, hM, hreg⟩ := region_estimates hd
  obtain ⟨δi, hδi, hinv⟩ := rectangleInversion_main d hd
  let N := max L M
  have hN : 0 < N := lt_of_lt_of_le (by linarith : 0 < L) (le_max_left _ _)
  let δ := min δi (1 / (8 * N))
  refine ⟨δ, L, lt_min hδi (by positivity), hL, ?_⟩
  intro e x y he hsmall hx hy
  have hx1 : |x| ≤ 1 := by linarith
  have hy1 : |y| ≤ 1 := by linarith
  have heN : 8 * e * N ≤ 1 := by
    have hb : e < 1 / (8 * N) := hsmall.trans_le (min_le_right _ _)
    have hc := (lt_div_iff₀ (by positivity : 0 < 8 * N)).mp hb
    nlinarith only [hc]
  have hML : 8 * e * M ≤ 1 := by
    have hb := mul_le_mul_of_nonneg_left (le_max_right L M)
      (show 0 ≤ 8 * e by positivity)
    exact hb.trans heN
  have hLL : 4 * e * L ≤ 1 := by
    have hb := mul_le_mul_of_nonneg_left (le_max_left L M)
      (show 0 ≤ 8 * e by positivity)
    have hL0 : 0 ≤ L := by linarith
    nlinarith [mul_nonneg he hL0]
  obtain ⟨hay, hPy, _⟩ := hreg y 0 y hy1 (by norm_num) (by positivity) hy1
  have hcy : |ceilingCoefficient d y| ≤ M := by
    have hid : ceilingCoefficient d y = -a d y 0 := by
      unfold ceilingCoefficient ceilingConstant ceilingQuadratic a radius
      ring
    rwa [hid, abs_neg]
  have hθ := threshold_abs_bound hd he hM hML hx1 hy1 hcy hPy
  have htilt : |e * x| ≤ e := by
    rw [abs_mul, abs_of_nonneg he]
    exact mul_le_of_le_one_right he hx1
  have hsi : |e * x| < δi := htilt.trans_lt (hsmall.trans_le (min_le_left _ _))
  obtain ⟨p, hp, huniq⟩ := (hinv (e * x) hsi).1 y (threshold d e x y) hy hθ
  have hY : y = p 0 + e * x * a d (p 0) (p 1) := by
    exact (congrArg (fun z : Plane => z 0) hp.2).symm
  have hT : p 1 + e * x * b d (p 0) (p 1) =
      e * alpha d * x * y + e ^ 2 *
        (alpha d * x ^ 2 * ceilingCoefficient d y - ceilingPolynomial d y) := by
    exact congrArg (fun z : Plane => z 1) hp.2
  have hest := hexp e x y (p 0) (p 1) he hLL hx1 hy1 hp.1.1 hp.1.2.1 hp.1.2.2 hY hT
  refine ⟨p, ⟨hp.1, hp.2, hest⟩, ?_⟩
  intro q hq
  exact huniq q ⟨hq.1, hq.2.1⟩

end SlopeRational.Threshold

end OAI
