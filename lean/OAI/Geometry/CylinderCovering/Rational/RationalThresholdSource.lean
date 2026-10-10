import OAI.Geometry.CylinderCovering.Rational.Coverage
import OAI.Geometry.CylinderCovering.Rational.ThresholdExpansion

namespace OAI

noncomputable section
open Set

namespace SlopeRational.ThresholdSource

theorem actual_inverse_expansions {d : ℝ} (hd : 0 < d) :
    ∃ δ L : ℝ, 0 < δ ∧ 1 ≤ L ∧
      ∀ e x y : ℝ, 0 ≤ e → e < δ → |x| ≤ 1 / 2 → |y| ≤ 1 / 2 →
        ∃! p : Plane,
          p ∈ inverseRectangle d ∧
          tiltedMap d (e * x) p = vec2 y (threshold d e x y) ∧
          |p 0 - y| ≤ e * L ∧
          |p 1| ≤ 3 * L * e ^ 2 ∧
          |p 0 - y - e * x * ceilingCoefficient d y| ≤ 4 * L ^ 2 * e ^ 2 ∧
          |b d (p 0) (p 1) - alpha d * y -
            e * alpha d * x * ceilingCoefficient d y| ≤ 7 * L ^ 2 * e ^ 2 ∧
          |p 1 + e ^ 2 * ceilingPolynomial d y| ≤ 9 * L ^ 2 * e ^ 3 ∧
          |p 1 + e ^ 2 * ceilingPolynomial d (p 0)| ≤ 8 * L ^ 2 * e ^ 3 := by
  obtain ⟨L, hL, hreg⟩ := Threshold.region_estimates hd
  obtain ⟨δi, hδi, hinv⟩ := rectangleInversion_main d hd
  have hLpos : 0 < L := by linarith
  let δ := min δi (1 / (8 * L))
  refine ⟨δ, L, lt_min hδi (by positivity), hL, ?_⟩
  intro e x y he heδ hx hy
  have heBound : e < 1 / (8 * L) := heδ.trans_le (min_le_right _ _)
  have he8 : 8 * e * L ≤ 1 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 8 * L)).mp heBound
    nlinarith only [h]
  have he1 : e ≤ 1 := by nlinarith
  have hx1 : |x| ≤ 1 := by linarith
  have hy1 : |y| ≤ 1 := by linarith
  have htilt : |e * x| ≤ e := by
    rw [abs_mul, abs_of_nonneg he]
    exact mul_le_of_le_one_right he hx1
  have hsi : |e * x| < δi := htilt.trans_lt (heδ.trans_le (min_le_left _ _))
  obtain ⟨hay, hPy, _⟩ := hreg y 0 y hy1 (by norm_num) (by positivity) hy1
  have hcy : |ceilingCoefficient d y| ≤ L := by
    rw [ceilingCoefficient_eq, abs_neg]
    exact hay
  have hθ : |threshold d e x y| ≤ 1 / 2 :=
    threshold_abs_bound hd he hL he8 hx1 hy1 hcy hPy
  obtain ⟨p, hp, huniq⟩ := (hinv (e * x) hsi).1 y (threshold d e x y) hy hθ
  have hY : y = p 0 + e * x * a d (p 0) (p 1) := by
    exact (congrArg (fun z : Plane => z 0) hp.2).symm
  have hT : p 1 + e * x * b d (p 0) (p 1) =
      e * alpha d * x * y + e ^ 2 *
        (alpha d * x ^ 2 * ceilingCoefficient d y - ceilingPolynomial d y) := by
    exact congrArg (fun z : Plane => z 1) hp.2
  obtain ⟨ha, hP, haLip, hbLip, hPLip⟩ :=
    hreg (p 0) (p 1) y hp.1.1 hp.1.2.1 hp.1.2.2 hy1
  have hα : |alpha d| ≤ 1 := by
    unfold alpha
    rw [abs_of_pos (by positivity : 0 < 1 / (1 + 2 * d))]
    exact (div_le_one (by positivity : 0 < 1 + 2 * d)).2 (by linarith)
  have hrest := CylinderCovering.ThresholdRemainder.inverse_threshold_remainder
    he hL (by linarith : 4 * e * L ≤ 1) hx1 hα
    ha hP haLip hbLip hPLip hY hT
  have hdis : |p 0 - y| ≤ e * L := by
    have hid : p 0 - y = -(e * x * a d (p 0) (p 1)) := by linarith only [hY]
    rw [hid, abs_neg, abs_mul, abs_mul, abs_of_nonneg he]
    calc
      e * |x| * |a d (p 0) (p 1)| ≤ e * 1 * L := by gcongr
      _ = e * L := by ring
  have hhorizontal := CylinderCovering.ThresholdRemainder.inverse_horizontal_expansion
    he he1 hLpos.le hx1 ha haLip hY hrest.1
  have hfield := CylinderCovering.ThresholdRemainder.inverse_field_expansion
    hLpos.le hα hbLip hrest.1 hhorizontal
  have hPyerr : |p 1 + e ^ 2 * ceilingPolynomial d y| ≤ 9 * L ^ 2 * e ^ 3 := by
    have hpoly : |ceilingPolynomial d (p 0) - ceilingPolynomial d y| ≤ L ^ 2 * e := by
      exact hPLip.trans (by nlinarith only [mul_le_mul_of_nonneg_left hdis hLpos.le])
    have hid : p 1 + e ^ 2 * ceilingPolynomial d y =
        (p 1 + e ^ 2 * ceilingPolynomial d (p 0)) -
          e ^ 2 * (ceilingPolynomial d (p 0) - ceilingPolynomial d y) := by ring
    rw [hid]
    calc
      _ ≤ |p 1 + e ^ 2 * ceilingPolynomial d (p 0)| +
          |e ^ 2 * (ceilingPolynomial d (p 0) - ceilingPolynomial d y)| := abs_sub _ _
      _ ≤ 8 * L ^ 2 * e ^ 3 + e ^ 2 * (L ^ 2 * e) := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg e)]
        exact add_le_add hrest.2 (mul_le_mul_of_nonneg_left hpoly (sq_nonneg e))
      _ = 9 * L ^ 2 * e ^ 3 := by ring
  refine ⟨p, ⟨hp.1, hp.2, hdis, hrest.1, hhorizontal, hfield, hPyerr, hrest.2⟩, ?_⟩
  intro q hq
  exact huniq q ⟨hq.1, hq.2.1⟩

theorem labelDomain_subset_rectangle {d : ℝ} (hd : 0 < d) (e q : ℝ) :
    labelDomain d e q ⊆ inverseRectangle d := by
  intro p hp
  have hw : 2 * |p 0| ≤ 1 / 2 - p 1 := hp.1
  have ht : -(1 / 4 : ℝ) ≤ p 1 := hp.2.1
  change |p 0| ≤ 1 ∧ -1 ≤ p 1 ∧ p 1 ≤ 1 / 2 + d / 2
  refine ⟨by linarith, by linarith, ?_⟩
  linarith [abs_nonneg (p 0)]

theorem actual_threshold_unique {d : ℝ} (hd : 0 < d) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ e q x y t : ℝ, 0 < e → e < δ → C * e ^ 3 ≤ q →
        |x| ≤ 1 / 2 → |y| ≤ 1 / 2 → |t| ≤ 1 / 2 →
        vec2 y t ∈ wedge → threshold d e x y ≤ t →
        ∃! p : Plane, p ∈ labelDomain d e q ∧ tiltedMap d (e * x) p = vec2 y t := by
  obtain ⟨δc, C, hδc, hC, hinc⟩ := thresholdInclusion_main d hd
  obtain ⟨δi, hδi, hinv⟩ := rectangleInversion_main d hd
  refine ⟨min δc δi, C, lt_min hδc hδi, hC, ?_⟩
  intro e q x y t he heδ hq hx hy ht hw hθ
  obtain ⟨p, hp, hmap⟩ := hinc e q x y t he
    (heδ.trans_le (min_le_left _ _)) hq hx hy ht hw hθ
  have htilt : |e * x| ≤ e := by
    rw [abs_mul, abs_of_pos he]
    exact mul_le_of_le_one_right he.le (by linarith : |x| ≤ 1)
  have hsi : |e * x| < δi := htilt.trans_lt (heδ.trans_le (min_le_right _ _))
  obtain ⟨r, hr, huniq⟩ := (hinv (e * x) hsi).1 y t hy ht
  refine ⟨p, ⟨hp, hmap⟩, ?_⟩
  intro p' hp'
  have hpr := huniq p ⟨labelDomain_subset_rectangle hd e q hp, hmap⟩
  have hp'r := huniq p' ⟨labelDomain_subset_rectangle hd e q hp'.1, hp'.2⟩
  exact hp'r.trans hpr.symm

theorem fixed_quadratic_threshold_unique {d η : ℝ} (hd : 0 < d) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ e x y t : ℝ, 0 < e → e < δ →
        |x| ≤ 1 / 2 → |y| ≤ 1 / 2 → |t| ≤ 1 / 2 →
        vec2 y t ∈ wedge → threshold d e x y ≤ t →
        ∃! p : Plane,
          p ∈ labelDomain d e (η * e ^ 2) ∧ tiltedMap d (e * x) p = vec2 y t := by
  obtain ⟨δc, C, hδc, hC, hinc⟩ := actual_threshold_unique hd
  refine ⟨min δc (η / C), lt_min hδc (div_pos hη hC), ?_⟩
  intro e x y t he heδ hx hy ht hw hθ
  have hmargin : e * C < η :=
    (lt_div_iff₀ hC).mp (heδ.trans_le (min_le_right _ _))
  have hpad : C * e ^ 3 ≤ η * e ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hmargin.le (sq_nonneg e)
    nlinarith only [h]
  exact hinc e (η * e ^ 2) x y t he (heδ.trans_le (min_le_left _ _))
    hpad hx hy ht hw hθ

theorem fixed_quadratic_sweep_coverage {d η : ℝ} (hd : 0 < d) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ e : ℝ, 0 < e → e < δ →
      referenceTetrahedron ⊆ lowerSweep d e (η * e ^ 2) ∪ upperSweep d e (η * e ^ 2) := by
  obtain ⟨δc, C, hδc, hC, hcover⟩ := rational_cover_small hd
  refine ⟨min δc (η / C), lt_min hδc (div_pos hη hC), ?_⟩
  intro e he heδ
  have hmargin : e * C < η :=
    (lt_div_iff₀ hC).mp (heδ.trans_le (min_le_right _ _))
  have hpad : C * e ^ 3 ≤ η * e ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hmargin.le (sq_nonneg e)
    nlinarith only [h]
  exact hcover e (η * e ^ 2) he (heδ.trans_le (min_le_left _ _)) hpad

end SlopeRational.ThresholdSource

end

end OAI
