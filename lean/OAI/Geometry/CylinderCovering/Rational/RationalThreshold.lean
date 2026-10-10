import OAI.Geometry.CylinderCovering.Rational.ThresholdDefinitions
import OAI.Geometry.CylinderCovering.Rational.ThresholdBounds
import OAI.Geometry.CylinderCovering.Rational.Inversion
import OAI.Geometry.CylinderCovering.Rational.Wedge

namespace OAI

noncomputable section
namespace SlopeRational
open Set

theorem threshold_sum_nonpos {d : ℝ} (hd : 0 < d) (ε x y : ℝ) :
    threshold d ε x y + threshold d ε (-y) x ≤ 0 := by
  have hid : threshold d ε x y + threshold d ε (-y) x =
      -ε ^ 2 * alpha d * ceilingQuadratic d * (x ^ 2 - y ^ 2) ^ 2 := by
    unfold threshold ceilingPolynomial ceilingCoefficient
    ring
  rw [hid]
  have hα : 0 ≤ alpha d := by unfold alpha; positivity
  have hc : 0 ≤ ceilingQuadratic d := by unfold ceilingQuadratic; positivity
  nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg ε) hα) hc)
    (sq_nonneg (x ^ 2 - y ^ 2))]

theorem threshold_alternative {d : ℝ} (hd : 0 < d) (ε x y t : ℝ) :
    threshold d ε x y ≤ t ∨ threshold d ε (-y) x ≤ -t := by
  have h := threshold_sum_nonpos hd ε x y
  by_cases ht : threshold d ε x y ≤ t
  · exact Or.inl ht
  · exact Or.inr (by linarith)

private theorem alpha_abs_le_one {d : ℝ} (hd : 0 < d) : |alpha d| ≤ 1 := by
  unfold alpha
  rw [abs_of_pos (by positivity : 0 < 1 / (1 + 2 * d))]
  exact (div_le_one (by positivity : 0 < 1 + 2 * d)).2 (by linarith)

theorem threshold_abs_bound {d ε x y L : ℝ} (hd : 0 < d)
    (he : 0 ≤ ε) (hL : 1 ≤ L) (hsmall : 8 * ε * L ≤ 1)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hc : |ceilingCoefficient d y| ≤ L) (hP : |ceilingPolynomial d y| ≤ L) :
    |threshold d ε x y| ≤ 1 / 2 := by
  have hL0 : 0 ≤ L := by linarith
  have heL : ε * L ≤ 1 / 8 := by linarith
  have he1 : ε ≤ 1 / 8 := by nlinarith
  have hα := alpha_abs_le_one hd
  have hx2 : |x| ^ 2 ≤ 1 := by nlinarith only [abs_nonneg x, hx]
  have hlead : |ε * alpha d * x * y| ≤ ε := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg he]
    calc
      ε * |alpha d| * |x| * |y| ≤ ε * 1 * 1 * 1 := by gcongr
      _ = ε := by ring
  have hsecond : |alpha d * x ^ 2 * ceilingCoefficient d y - ceilingPolynomial d y| ≤ 2 * L := by
    calc
      _ ≤ |alpha d * x ^ 2 * ceilingCoefficient d y| + |ceilingPolynomial d y| := abs_sub _ _
      _ = |alpha d| * |x| ^ 2 * |ceilingCoefficient d y| + |ceilingPolynomial d y| := by
        simp only [abs_mul, abs_pow]
      _ ≤ 1 * 1 * L + L := by gcongr
      _ = 2 * L := by ring
  have hquadratic : |ε ^ 2 *
      (alpha d * x ^ 2 * ceilingCoefficient d y - ceilingPolynomial d y)| ≤ ε ^ 2 * (2 * L) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    exact mul_le_mul_of_nonneg_left hsecond (sq_nonneg ε)
  have hsum := abs_add_le (ε * alpha d * x * y)
    (ε ^ 2 * (alpha d * x ^ 2 * ceilingCoefficient d y - ceilingPolynomial d y))
  have hεL := mul_le_mul_of_nonneg_right heL he
  unfold threshold
  nlinarith only [hsum, hlead, hquadratic, hεL, he1]

private theorem horizontal_displacement {d ε x y : ℝ} {p : Plane}
    (he : 0 ≤ ε) (hx : |x| ≤ 1) {L : ℝ} (ha : |a d (p 0) (p 1)| ≤ L)
    (hmap : tiltedMap d (ε * x) p = vec2 y (tiltedMap d (ε * x) p 1)) :
    |p 0 - y| ≤ ε * L := by
  have h := congrArg (fun z : Plane => z 0) hmap
  change p 0 + ε * x * a d (p 0) (p 1) = y at h
  have hid : p 0 - y = -(ε * x * a d (p 0) (p 1)) := by linarith
  rw [hid, abs_neg, abs_mul, abs_mul, abs_of_nonneg he]
  calc
    ε * |x| * |a d (p 0) (p 1)| ≤ ε * 1 * L := by gcongr
    _ = ε * L := by ring

theorem threshold_inclusion_of_wedge {d : ℝ} (hd : 0 < d)
    (hwedge : ∃ δ > 0, ∀ s : ℝ, |s| < δ → ∀ p ∈ inverseRectangle d,
      tiltedMap d s p ∈ wedge → p ∈ wedge) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ ε q x y t : ℝ, 0 < ε → ε < δ → 10 * C * ε ^ 3 ≤ q →
        |x| ≤ 1 / 2 → |y| ≤ 1 / 2 → |t| ≤ 1 / 2 →
        vec2 y t ∈ wedge → threshold d ε x y ≤ t →
        ∃ p ∈ labelDomain d ε q, tiltedMap d (ε * x) p = vec2 y t := by
  obtain ⟨L, hL, hreg⟩ := Threshold.region_estimates hd
  obtain ⟨δi, hδi, hinv⟩ := rectangleInversion_main d hd
  obtain ⟨δw, hδw, hw⟩ := hwedge
  have hLpos : 0 < L := by linarith
  let δ := min δi (min δw (1 / (8 * L)))
  have hδ : 0 < δ := lt_min hδi (lt_min hδw (by positivity))
  refine ⟨δ, L ^ 2, hδ, sq_pos_of_pos hLpos, ?_⟩
  intro ε q x y t he hsmall hq hx hy ht htarget hthreshold
  have he1 : ε < 1 / (8 * L) := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have he8 : 8 * ε * L ≤ 1 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 8 * L)).mp he1
    nlinarith only [h]
  have heL : ε * L ≤ 1 / 8 := by linarith
  have heBound : ε ≤ 1 / 8 := by nlinarith
  have hcut : 12 * L * ε ^ 2 ≤ 1 := by
    have h := mul_le_mul heBound heL (mul_nonneg he.le hLpos.le) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    nlinarith only [h]
  have hx1 : |x| ≤ 1 := by linarith
  have hy1 : |y| ≤ 1 := by linarith
  have htilt : |ε * x| ≤ ε := by
    rw [abs_mul, abs_of_pos he]
    exact mul_le_of_le_one_right he.le hx1
  have hsi : |ε * x| < δi := htilt.trans_lt (hsmall.trans_le (min_le_left _ _))
  have hsw : |ε * x| < δw := htilt.trans_lt
    (hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨hay, hPy, _⟩ := hreg y 0 y hy1 (by norm_num) (by positivity) hy1
  have hcy : |ceilingCoefficient d y| ≤ L := by
    have hid : ceilingCoefficient d y = -a d y 0 := by
      unfold ceilingCoefficient ceilingConstant ceilingQuadratic a radius
      ring
    rw [hid, abs_neg]
    exact hay
  have hθ : |threshold d ε x y| ≤ 1 / 2 :=
    threshold_abs_bound hd he.le hL he8 hx1 hy1 hcy hPy
  obtain ⟨p, hp, hpuniq⟩ := (hinv (ε * x) hsi).1 y t hy ht
  obtain ⟨p₀, hp₀, _⟩ := (hinv (ε * x) hsi).1 y (threshold d ε x y) hy hθ
  have hpy : y = p₀ 0 + ε * x * a d (p₀ 0) (p₀ 1) := by
    have h := congrArg (fun z : Plane => z 0) hp₀.2
    exact h.symm
  have hpt : p₀ 1 + ε * x * b d (p₀ 0) (p₀ 1) =
      ε * alpha d * x * y + ε ^ 2 *
        (alpha d * x ^ 2 * ceilingCoefficient d y - ceilingPolynomial d y) := by
    have h := congrArg (fun z : Plane => z 1) hp₀.2
    exact h
  obtain ⟨ha₀, hP₀, haLip, hbLip, hPLip⟩ :=
    hreg (p₀ 0) (p₀ 1) y hp₀.1.1 hp₀.1.2.1 hp₀.1.2.2 hy1
  have hrest := CylinderCovering.ThresholdRemainder.inverse_threshold_remainder
    he.le hL (by linarith : 4 * ε * L ≤ 1) hx1 (alpha_abs_le_one hd)
      ha₀ hP₀ haLip hbLip hPLip hpy hpt
  have hmon : p₀ 1 ≤ p 1 := by
    rcases lt_or_eq_of_le hthreshold with hlt | heq
    · apply le_of_lt
      apply (hinv (ε * x) hsi).2 p₀ hp₀.1 p hp.1
      · rw [hp₀.2, hp.2]
        rfl
      · rw [hp₀.2, hp.2]
        exact hlt
    · have heqp : p₀ = p := hpuniq p₀ ⟨hp₀.1, by rw [hp₀.2, heq]⟩
      rw [heqp]
  have hpmap : tiltedMap d (ε * x) p = vec2 y (tiltedMap d (ε * x) p 1) := by
    rw [hp.2]
    rfl
  have hp₀map : tiltedMap d (ε * x) p₀ = vec2 y (tiltedMap d (ε * x) p₀ 1) := by
    rw [hp₀.2]
    rfl
  have hap := (hreg (p 0) (p 1) y hp.1.1 hp.1.2.1 hp.1.2.2 hy1).1
  have hdisp := horizontal_displacement he.le hx1 hap hpmap
  have hdisp₀ := horizontal_displacement he.le hx1 ha₀ hp₀map
  have hbetween : |p 0 - p₀ 0| ≤ 2 * ε * L := by
    have h := abs_sub_le (p 0) y (p₀ 0)
    rw [abs_sub_comm y (p₀ 0)] at h
    linarith
  have hpolyLip := (hreg (p 0) (p 1) (p₀ 0) hp.1.1 hp.1.2.1 hp.1.2.2 hp₀.1.1).2.2.2.2
  have hPchange : |ceilingPolynomial d (p 0) - ceilingPolynomial d (p₀ 0)| ≤ 2 * L ^ 2 * ε := by
    exact hpolyLip.trans (by nlinarith only [mul_le_mul_of_nonneg_left hbetween hLpos.le])
  have hlow := CylinderCovering.ThresholdRemainder.padding_absorbs_above_threshold_general
    hrest.1 hrest.2 hmon hPchange hq hcut
  refine ⟨p, ⟨?_, hlow.1, hlow.2⟩, hp.2⟩
  apply hw (ε * x) hsw p hp.1
  rwa [hp.2]

theorem thresholdInclusion_main : ThresholdInclusionStatement := by
  intro d hd
  obtain ⟨δw, hδw, hw⟩ := rectangleWedge_main d hd
  have hwedge : ∃ δ > 0, ∀ s : ℝ, |s| < δ → ∀ p ∈ inverseRectangle d,
      tiltedMap d s p ∈ wedge → p ∈ wedge :=
    ⟨δw, hδw, fun s hs p hp => (hw s hs p hp).mp⟩
  obtain ⟨δ, C, hδ, hC, hinc⟩ := threshold_inclusion_of_wedge hd hwedge
  refine ⟨δ, 10 * C, hδ, by positivity, ?_⟩
  intro ε q x y t he hεδ hq hx hy ht hwedge hthreshold
  exact hinc ε q x y t he hεδ hq hx hy ht hwedge hthreshold

end SlopeRational

end

end OAI
