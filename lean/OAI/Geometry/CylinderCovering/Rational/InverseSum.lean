import OAI.Geometry.CylinderCovering.Rational.ThresholdExpansion

namespace OAI

noncomputable section
namespace SlopeRational.InverseSum

private lemma displacement {e x y Y a : ℝ} (he : 0 ≤ e)
    (hx : |x| ≤ 1) (ha : |a| ≤ 1 / 8) (h : y = Y + e * x * a) :
    |Y - y| ≤ e / 8 := by
  have hid : Y - y = -(e * x * a) := by rw [h]; ring
  rw [hid, abs_neg, abs_mul, abs_mul, abs_of_nonneg he]
  calc
    e * |x| * |a| ≤ e * 1 * (1 / 8) := by gcongr
    _ = e / 8 := by ring

private lemma two_error_bound {e x y P Q B : ℝ}
    (he : 0 ≤ e) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hP : |P| ≤ B) (hQ : |Q| ≤ B) :
    |e * (y * P - x * Q)| ≤ 2 * e * B := by
  rw [abs_mul, abs_of_nonneg he]
  calc
    e * |y * P - x * Q| ≤ e * (|y * P| + |x * Q|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) he
    _ = e * (|y| * |P| + |x| * |Q|) := by rw [abs_mul, abs_mul]
    _ ≤ e * (1 * B + 1 * B) := by gcongr
    _ = 2 * e * B := by ring

theorem actual_inverse_sum {d : ℝ} (hd : 0 < d) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (e x y t : ℝ) (P Q : Plane),
        0 ≤ e → e < δ → |x| ≤ 1 / 2 → |y| ≤ 1 / 2 →
        P ∈ wedge → Q ∈ wedge → P 1 ≤ 0 → Q 1 ≤ 0 →
        tiltedMap d (e * x) P = vec2 y t →
        tiltedMap d (-e * y) Q = vec2 x (-t) →
        |P 1 + Q 1 + e ^ 2 * alpha d *
          (x ^ 2 * ceilingCoefficient d y + y ^ 2 * ceilingCoefficient d x)| ≤
          C * e ^ 3 := by
  obtain ⟨L, hL, hreg⟩ := Threshold.region_estimates hd
  have hLpos : 0 < L := by linarith
  refine ⟨min 1 (1 / (2 * L)), 14 * L ^ 2,
    lt_min (by norm_num) (by positivity), by positivity, ?_⟩
  intro e x y t P Q he heδ hx hy hPw hQw hP0 hQ0 hPm hQm
  have he1 : e ≤ 1 := le_of_lt (heδ.trans_le (min_le_left _ _))
  have heL : e * L ≤ 1 / 2 := by
    have h := (lt_div_iff₀ (show 0 < 2 * L by positivity)).mp
      (heδ.trans_le (min_le_right _ _))
    linarith
  have hx1 : |x| ≤ 1 := by linarith
  have hy1 : |y| ≤ 1 := by linarith
  have hα : |alpha d| ≤ 1 := by
    unfold alpha
    rw [abs_of_pos (by positivity : 0 < 1 / (1 + 2 * d))]
    exact (div_le_one (by positivity : 0 < 1 + 2 * d)).2 (by linarith)
  obtain ⟨haP0, haP1, hbP⟩ := field_coordinate_bounds hd hPw
  obtain ⟨haQ0, haQ1, hbQ⟩ := field_coordinate_bounds hd hQw
  have haP : |a d (P 0) (P 1)| ≤ 1 / 8 := abs_le.mpr ⟨haP0, by linarith⟩
  have haQ : |a d (Q 0) (Q 1)| ≤ 1 / 8 := abs_le.mpr ⟨haQ0, by linarith⟩
  have hY : y = P 0 + e * x * a d (P 0) (P 1) :=
    (congrArg (fun z : Plane => z 0) hPm).symm
  have hX : x = Q 0 + e * (-y) * a d (Q 0) (Q 1) := by
    have h := congrArg (fun z : Plane => z 0) hQm
    change Q 0 + (-e * y) * a d (Q 0) (Q 1) = x at h
    nlinarith only [h]
  have hT := congrArg (fun z : Plane => z 1) hPm
  have hR := congrArg (fun z : Plane => z 1) hQm
  change P 1 + e * x * b d (P 0) (P 1) = t at hT
  change Q 1 + (-e * y) * b d (Q 0) (Q 1) = -t at hR
  have hsum : P 1 + Q 1 = e *
      (y * b d (Q 0) (Q 1) - x * b d (P 0) (P 1)) := by
    nlinarith only [hT, hR]
  have hdisP := displacement he hx1 haP hY
  have hdisQ := displacement he (by simpa using hy1) haQ hX
  have hPcoord : |P 0| ≤ 1 := by
    have h := abs_add_le (P 0 - y) y
    have hid : P 0 - y + y = P 0 := by ring
    rw [hid] at h
    linarith
  have hQcoord : |Q 0| ≤ 1 := by
    have h := abs_add_le (Q 0 - x) x
    have hid : Q 0 - x + x = Q 0 := by ring
    rw [hid] at h
    linarith
  have hsumabs : |P 1 + Q 1| = |P 1| + |Q 1| := by
    rw [abs_of_nonpos hP0, abs_of_nonpos hQ0,
      abs_of_nonpos (add_nonpos hP0 hQ0)]
    ring
  have hrough : |P 1| + |Q 1| ≤ e / 2 := by
    rw [← hsumabs, hsum]
    have h := two_error_bound he hx1 hy1 hbQ hbP
    nlinarith only [h]
  have hPlo : -1 ≤ P 1 := by
    rw [abs_of_nonpos hP0, abs_of_nonpos hQ0] at hrough
    linarith
  have hQlo : -1 ≤ Q 1 := by
    rw [abs_of_nonpos hP0, abs_of_nonpos hQ0] at hrough
    linarith
  obtain ⟨haPr, _, haPLip, hbPLip, _⟩ :=
    hreg (P 0) (P 1) y hPcoord hPlo (by linarith) hy1
  obtain ⟨haQr, _, haQLip, hbQLip, _⟩ :=
    hreg (Q 0) (Q 1) x hQcoord hQlo (by linarith) hx1
  have hbPnear : |b d (P 0) (P 1) - alpha d * y| ≤ L * |P 1| + e / 8 := by
    have hid : b d (P 0) (P 1) - alpha d * y =
        (b d (P 0) (P 1) - alpha d * P 0) + alpha d * (P 0 - y) := by ring
    rw [hid]
    calc
      _ ≤ |b d (P 0) (P 1) - alpha d * P 0| + |alpha d * (P 0 - y)| :=
        abs_add_le _ _
      _ ≤ L * |P 1| + 1 * (e / 8) := by rw [abs_mul]; gcongr
      _ = _ := by ring
  have hbQnear : |b d (Q 0) (Q 1) - alpha d * x| ≤ L * |Q 1| + e / 8 := by
    have hid : b d (Q 0) (Q 1) - alpha d * x =
        (b d (Q 0) (Q 1) - alpha d * Q 0) + alpha d * (Q 0 - x) := by ring
    rw [hid]
    calc
      _ ≤ |b d (Q 0) (Q 1) - alpha d * Q 0| + |alpha d * (Q 0 - x)| :=
        abs_add_le _ _
      _ ≤ L * |Q 1| + 1 * (e / 8) := by rw [abs_mul]; gcongr
      _ = _ := by ring
  have hboot : |P 1| + |Q 1| ≤ e * (L * (|P 1| + |Q 1|) + e / 4) := by
    conv_lhs => rw [← hsumabs, hsum]
    have hid : y * b d (Q 0) (Q 1) - x * b d (P 0) (P 1) =
        y * (b d (Q 0) (Q 1) - alpha d * x) -
          x * (b d (P 0) (P 1) - alpha d * y) := by ring
    rw [hid, abs_mul, abs_of_nonneg he]
    calc
      _ ≤ e * (|y * (b d (Q 0) (Q 1) - alpha d * x)| +
          |x * (b d (P 0) (P 1) - alpha d * y)|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) he
      _ ≤ e * (1 * (L * |Q 1| + e / 8) + 1 * (L * |P 1| + e / 8)) := by
        rw [abs_mul, abs_mul]
        gcongr
      _ = _ := by ring
  have hsmallS := mul_le_mul_of_nonneg_right heL
    (add_nonneg (abs_nonneg (P 1)) (abs_nonneg (Q 1)))
  have hquadratic : |P 1| + |Q 1| ≤ e ^ 2 / 2 := by
    nlinarith only [hboot, hsmallS]
  have hscale : e ^ 2 / 2 ≤ 3 * L * e ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hL (sq_nonneg e), sq_nonneg e]
  have hPh : |P 1| ≤ 3 * L * e ^ 2 := by linarith [abs_nonneg (Q 1)]
  have hQh : |Q 1| ≤ 3 * L * e ^ 2 := by linarith [abs_nonneg (P 1)]
  have hPe := CylinderCovering.ThresholdRemainder.inverse_horizontal_expansion
    he he1 hLpos.le hx1 haPr haPLip hY hPh
  have hQe := CylinderCovering.ThresholdRemainder.inverse_horizontal_expansion
    he he1 hLpos.le (by simpa using hy1) haQr haQLip hX hQh
  have hPb := CylinderCovering.ThresholdRemainder.inverse_field_expansion
    hLpos.le hα hbPLip hPh hPe
  have hQb := CylinderCovering.ThresholdRemainder.inverse_field_expansion
    hLpos.le hα hbQLip hQh hQe
  have hfinal := two_error_bound he hx1 hy1 hQb hPb
  have hid : P 1 + Q 1 + e ^ 2 * alpha d *
      (x ^ 2 * ceilingCoefficient d y + y ^ 2 * ceilingCoefficient d x) =
      e * (y * (b d (Q 0) (Q 1) - alpha d * x -
          e * alpha d * (-y) * ceilingCoefficient d x) -
        x * (b d (P 0) (P 1) - alpha d * y -
          e * alpha d * x * ceilingCoefficient d y)) := by
    rw [hsum]
    ring
  rw [hid]
  convert hfinal using 1
  ring

end SlopeRational.InverseSum

end

end OAI
