import OAI.Geometry.CylinderCovering.Convexity.GeneralCapAreaDefinitions
import OAI.Geometry.CylinderCovering.Angular.Taylor

namespace OAI

open MeasureTheory Set
open scoped Interval

namespace CylinderCovering.GeneralCapArea

lemma continuous_profile : Continuous profile := by unfold profile; fun_prop
lemma continuous_idealSpeed : Continuous idealSpeed := by unfold idealSpeed; fun_prop
lemma continuous_idealDensity (ε η : ℝ) : Continuous (idealDensity ε η) := by
  unfold idealDensity profile idealSpeed
  fun_prop

lemma coefficient_polynomial (η q : ℝ) :
    profile q + η - idealSpeed q / 8 =
      (η - 1 / 128) + (-1 / 64 : ℝ) * q ^ 2 + (7 / 128 : ℝ) * q ^ 4 := by
  unfold profile idealSpeed
  ring

lemma coefficient_integral (η : ℝ) :
    (∫ q in (-1 : ℝ)..1, profile q + η - idealSpeed q / 8) =
      2 * η - 1 / 240 := by
  simp_rw [coefficient_polynomial]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_pow, smul_eq_mul]
    norm_num
    ring
  · exact (continuous_const.intervalIntegrable _ _)
  · exact (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  · exact (continuous_const.add (continuous_const.mul (continuous_id.pow 2))).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_id.pow 4)).intervalIntegrable _ _

lemma idealDensity_integral (ε η : ℝ) :
    (∫ q in (-1 : ℝ)..1, idealDensity ε η q) =
      1 / 2 + (2 * η - 1 / 240) * ε ^ 2 := by
  unfold idealDensity
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, coefficient_integral]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  · exact continuous_const.intervalIntegrable _ _
  · exact (continuous_const.mul
      ((continuous_profile.add continuous_const).sub
        (continuous_idealSpeed.div_const 8))).intervalIntegrable _ _

lemma perturbed_product_remainder {z M A A₀ R E F : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hM0 : 0 ≤ M) (hM1 : M ≤ 1 / 4)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hE : 0 ≤ E)
    (hR : |R| ≤ 1) (hRE : |R - (1 / 2 + z * M)| ≤ E * z ^ 2)
    (hAF : |A - A₀| ≤ F * z) :
    |R ^ 2 / Real.sqrt (1 + z * A) - (1 / 4 + z * (M - A₀ / 8))| ≤
      (2 * E + F / 8 + 47 / 128) * z ^ 2 := by
  have hzM0 : 0 ≤ z * M := mul_nonneg hz0 hM0
  have hzM1 : z * M ≤ 1 / 4 := by
    nlinarith only [mul_le_mul hz1 hM1 hM0 (by norm_num : (0 : ℝ) ≤ 1)]
  have hbase : |(1 / 2 : ℝ) + z * M| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hsum : |R + (1 / 2 + z * M)| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith only [hR, hbase])
  have hsq : |R ^ 2 - (1 / 2 + z * M) ^ 2| ≤ 2 * E * z ^ 2 := by
    calc
      _ = |R - (1 / 2 + z * M)| * |R + (1 / 2 + z * M)| := by
        rw [← abs_mul]; congr 1; ring
      _ ≤ (E * z ^ 2) * 2 := mul_le_mul hRE hsum (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hsqrt : 1 ≤ Real.sqrt (1 + z * A) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith [mul_nonneg hz0 hA0])
  have hradial : |R ^ 2 / Real.sqrt (1 + z * A) -
      (1 / 2 + z * M) ^ 2 / Real.sqrt (1 + z * A)| ≤ 2 * E * z ^ 2 := by
    rw [← sub_div, abs_div, abs_of_nonneg (by linarith : 0 ≤ Real.sqrt (1 + z * A))]
    exact (div_le_self (abs_nonneg _) hsqrt).trans hsq
  have hspeed : |(1 / 4 + z * (M - A / 8)) -
      (1 / 4 + z * (M - A₀ / 8))| ≤ F / 8 * z ^ 2 := by
    calc
      _ = z / 8 * |A - A₀| := by
        have hid : (1 / 4 + z * (M - A / 8)) - (1 / 4 + z * (M - A₀ / 8)) =
            -(z / 8 * (A - A₀)) := by ring
        rw [hid, abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ z / 8)]
      _ ≤ z / 8 * (F * z) := mul_le_mul_of_nonneg_left hAF (by positivity)
      _ = _ := by ring
  have htaylor := AngularTaylor.bounded_product_remainder hz0 hz1 hM0 hM1 hA0 hA1
  have htri1 := abs_sub_le (R ^ 2 / Real.sqrt (1 + z * A))
    ((1 / 2 + z * M) ^ 2 / Real.sqrt (1 + z * A)) (1 / 4 + z * (M - A₀ / 8))
  have htri2 := abs_sub_le ((1 / 2 + z * M) ^ 2 / Real.sqrt (1 + z * A))
    (1 / 4 + z * (M - A / 8)) (1 / 4 + z * (M - A₀ / 8))
  nlinarith only [hradial, hspeed, htaylor, htri1, htri2]

lemma profile_bounds {q : ℝ} (hq : |q| ≤ 1) :
    0 ≤ profile q ∧ profile q ≤ 1 / 8 := by
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have hq4 : q ^ 4 ≤ 1 := by
    nlinarith [sq_nonneg q, mul_self_le_mul_self (sq_nonneg q) hq2]
  unfold profile
  constructor
  · positivity
  · linarith

lemma square_difference {x y E : ℝ} (hE : 0 ≤ E)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hxy : |x - y| ≤ E) :
    |x ^ 2 - y ^ 2| ≤ 2 * E := by
  have hsum : |x + y| ≤ 2 := (abs_add_le _ _).trans (by linarith only [hx, hy])
  calc
    _ = |x - y| * |x + y| := by rw [← abs_mul]; congr 1; ring
    _ ≤ E * 2 := mul_le_mul hxy hsum (abs_nonneg _) hE
    _ = _ := by ring

theorem capDensity_error {ε η C α β q : ℝ} {R : ℝ → ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 8) (hC : 0 ≤ C)
    (hε : ε ^ 2 ≤ 1) (hsmall : C * ε ^ 2 ≤ 1 / 16) (hq : |q| ≤ 1)
    (hα : |α - (1 + q ^ 2) / 4| ≤ C * ε ^ 2)
    (hβ : |β - q / 2| ≤ C * ε ^ 2)
    (hR : |R q - (1 / 2 + ε ^ 2 * (profile q + η))| ≤ C * ε ^ 4) :
    |capDensity ε α β R q - idealDensity ε η q| ≤ (3 * C + 1) * ε ^ 4 := by
  have hz0 : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hE : 0 ≤ C * ε ^ 2 := mul_nonneg hC hz0
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have ha00 : 0 ≤ (1 + q ^ 2) / 4 := by positivity
  have ha01 : (1 + q ^ 2) / 4 ≤ 1 / 2 := by linarith
  have ha0abs : |(1 + q ^ 2) / 4| ≤ 1 / 2 := by
    rw [abs_of_nonneg ha00]
    exact ha01
  have hb0abs : |q / 2| ≤ 1 / 2 := by
    rw [abs_div]
    norm_num
    linarith
  have haa : |α| ≤ 9 / 16 := by
    have h := abs_add_le (α - (1 + q ^ 2) / 4) ((1 + q ^ 2) / 4)
    rw [sub_add_cancel] at h
    linarith only [h, hα, ha0abs, hsmall]
  have hbb : |β| ≤ 9 / 16 := by
    have h := abs_add_le (β - q / 2) (q / 2)
    rw [sub_add_cancel] at h
    linarith only [h, hβ, hb0abs, hsmall]
  have ha2 : α ^ 2 ≤ 81 / 256 := by nlinarith [(abs_le.mp haa).1, (abs_le.mp haa).2]
  have hb2 : β ^ 2 ≤ 81 / 256 := by nlinarith [(abs_le.mp hbb).1, (abs_le.mp hbb).2]
  have hA0 : 0 ≤ α ^ 2 + 2 * β ^ 2 := by positivity
  have hA1 : α ^ 2 + 2 * β ^ 2 ≤ 1 := by linarith
  have hM0 : 0 ≤ profile q + η := add_nonneg (profile_bounds hq).1 hη0
  have hM1 : profile q + η ≤ 1 / 4 := by linarith [(profile_bounds hq).2]
  have hbase0 : 0 ≤ (1 / 2 : ℝ) + ε ^ 2 * (profile q + η) := by positivity
  have hbase1 : (1 / 2 : ℝ) + ε ^ 2 * (profile q + η) ≤ 3 / 4 := by
    nlinarith only [mul_le_mul hε hM1 hM0 (by norm_num : (0 : ℝ) ≤ 1)]
  have hCE4 : C * ε ^ 4 ≤ 1 / 16 := by
    have h := mul_le_mul_of_nonneg_left hε hE
    nlinarith only [h, hsmall]
  have hRabs : |R q| ≤ 1 := by
    have h := abs_add_le (R q - (1 / 2 + ε ^ 2 * (profile q + η)))
      (1 / 2 + ε ^ 2 * (profile q + η))
    rw [sub_add_cancel, abs_of_nonneg hbase0] at h
    linarith only [h, hR, hbase1, hCE4]
  have hαsq := square_difference hE (by linarith only [haa] : |α| ≤ 1)
    (by linarith only [ha0abs] : |(1 + q ^ 2) / 4| ≤ 1) hα
  have hβsq := square_difference hE (by linarith only [hbb] : |β| ≤ 1)
    (by linarith only [hb0abs] : |q / 2| ≤ 1) hβ
  have hspeed : |(α ^ 2 + 2 * β ^ 2) - idealSpeed q| ≤ (6 * C) * ε ^ 2 := by
    have hid : (α ^ 2 + 2 * β ^ 2) - idealSpeed q =
        (α ^ 2 - ((1 + q ^ 2) / 4) ^ 2) + 2 * (β ^ 2 - (q / 2) ^ 2) := by
      unfold idealSpeed
      ring
    rw [hid]
    have h := abs_add_le (α ^ 2 - ((1 + q ^ 2) / 4) ^ 2) (2 * (β ^ 2 - (q / 2) ^ 2))
    rw [abs_mul] at h
    norm_num at h
    linarith only [h, hαsq, hβsq]
  have hR' : |R q - (1 / 2 + ε ^ 2 * (profile q + η))| ≤ C * (ε ^ 2) ^ 2 := by
    convert hR using 1; ring
  have h := perturbed_product_remainder hz0 hε hM0 hM1 hA0 hA1 hC hRabs hR' hspeed
  unfold capDensity idealDensity
  calc
    _ ≤ (2 * C + (6 * C) / 8 + 47 / 128) * (ε ^ 2) ^ 2 := h
    _ ≤ (3 * C + 1) * ε ^ 4 := by
      have hp := mul_nonneg hC (sq_nonneg (ε ^ 2))
      nlinarith only [hp, sq_nonneg (ε ^ 2)]

lemma integral_error {f : ℝ → ℝ} {a b ε η L : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (herror : ∀ q ∈ Icc a b, |f q - idealDensity ε η q| ≤ L * ε ^ 4) :
    |(∫ q in a..b, f q) - (∫ q in a..b, idealDensity ε η q)| ≤
      L * ε ^ 4 * (b - a) := by
  rw [← intervalIntegral.integral_sub hf ((continuous_idealDensity ε η).intervalIntegrable a b)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := L * ε ^ 4)
    (f := fun q => f q - idealDensity ε η q) ?_
  · simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using h
  · intro q hq
    rw [uIoc_of_le hab] at hq
    simpa only [Real.norm_eq_abs] using herror q ⟨hq.1.le, hq.2⟩

theorem partition_area_error {N : ℕ} {a : ℕ → ℝ} {f : ℕ → ℝ → ℝ}
    {ε η L : ℝ} (ha0 : a 0 = -1) (haN : a N = 1)
    (ha : ∀ j < N, a j ≤ a (j + 1))
    (hf : ∀ j < N, IntervalIntegrable (f j) volume (a j) (a (j + 1)))
    (herror : ∀ j < N, ∀ q ∈ Icc (a j) (a (j + 1)),
      |f j q - idealDensity ε η q| ≤ L * ε ^ 4) :
    |(∑ j ∈ Finset.range N, ∫ q in a j..a (j + 1), f j q) -
      (1 / 2 + (2 * η - 1 / 240) * ε ^ 2)| ≤ 2 * L * ε ^ 4 := by
  have hideal : (∑ j ∈ Finset.range N, ∫ q in a j..a (j + 1), idealDensity ε η q) =
      1 / 2 + (2 * η - 1 / 240) * ε ^ 2 := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun j hj => (continuous_idealDensity ε η).intervalIntegrable (a j) (a (j + 1))),
      ha0, haN, idealDensity_integral]
  rw [← hideal, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        |(∫ q in a j..a (j + 1), f j q) -
          (∫ q in a j..a (j + 1), idealDensity ε η q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, L * ε ^ 4 * (a (j + 1) - a j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact integral_error (ha j (Finset.mem_range.mp hj))
        (hf j (Finset.mem_range.mp hj)) (herror j (Finset.mem_range.mp hj))
    _ = 2 * L * ε ^ 4 := by
      rw [← Finset.mul_sum, Finset.sum_range_sub, haN, ha0]
      ring

lemma partition_monotone {N : ℕ} {a : ℕ → ℝ}
    (ha : ∀ j < N, a j ≤ a (j + 1)) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) :
    a i ≤ a j := by
  have h : ∀ k ≥ i, k ≤ N → a i ≤ a k := by
    intro k hik
    induction k, hik using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ k hik ih =>
      intro hkN
      exact (ih (by omega)).trans (ha k (by omega))
  exact h j hij hj

theorem general_cap_area_expansion {N : ℕ} {a α β : ℕ → ℝ}
    {R : ℕ → ℝ → ℝ} {ε η C : ℝ}
    (ha0 : a 0 = -1) (haN : a N = 1)
    (ha : ∀ j < N, a j ≤ a (j + 1))
    (hRcont : ∀ j < N, ContinuousOn (R j) (Icc (a j) (a (j + 1))))
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 8) (hC : 0 ≤ C)
    (hε : ε ^ 2 ≤ 1) (hsmall : C * ε ^ 2 ≤ 1 / 16)
    (hα : ∀ j < N, ∀ q ∈ Icc (a j) (a (j + 1)),
      |α j - (1 + q ^ 2) / 4| ≤ C * ε ^ 2)
    (hβ : ∀ j < N, ∀ q ∈ Icc (a j) (a (j + 1)),
      |β j - q / 2| ≤ C * ε ^ 2)
    (hR : ∀ j < N, ∀ q ∈ Icc (a j) (a (j + 1)),
      |R j q - (1 / 2 + ε ^ 2 * (profile q + η))| ≤ C * ε ^ 4) :
    |(∑ j ∈ Finset.range N,
        ∫ q in a j..a (j + 1), capDensity ε (α j) (β j) (R j) q) -
      (1 / 2 + (2 * η - 1 / 240) * ε ^ 2)| ≤ 2 * (3 * C + 1) * ε ^ 4 := by
  apply partition_area_error ha0 haN ha
  · intro j hj
    apply ContinuousOn.intervalIntegrable_of_Icc (ha j hj)
    exact ((hRcont j hj).pow 2).div_const _
  · intro j hj q hq
    have haq : |q| ≤ 1 := by
      have hl : a 0 ≤ a j := partition_monotone ha (Nat.zero_le j) (by omega)
      have hu : a (j + 1) ≤ a N := partition_monotone ha (by omega) le_rfl
      rw [ha0] at hl
      rw [haN] at hu
      rw [abs_le]
      exact ⟨hl.trans hq.1, hq.2.trans hu⟩
    exact capDensity_error hη0 hη1 hC hε hsmall haq
      (hα j hj q hq) (hβ j hj q hq) (hR j hj q hq)

theorem strict_half_of_area_error {cost ε η L : ℝ}
    (hε : 0 < ε)
    (herror : |cost - (1 / 2 + (2 * η - 1 / 240) * ε ^ 2)| ≤ L * ε ^ 4)
    (hsmall : L * ε ^ 2 < 1 / 240 - 2 * η) : cost < 1 / 2 := by
  have hgap := mul_lt_mul_of_pos_right hsmall (sq_pos_of_pos hε)
  have hu := (abs_le.mp herror).2
  nlinarith only [hgap, hu]

theorem exists_uniform_smallness {η C : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1 / 480) (hC : 0 ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ε ≤ 1 / 2 ∧ (10 + 4 * C) * ε ≤ η ∧
      ε ^ 2 ≤ 1 ∧ C * ε ^ 2 ≤ 1 / 16 ∧
      2 * (3 * C + 1) * ε ^ 2 < 1 / 240 - 2 * η := by
  let g : ℝ := 1 / 240 - 2 * η
  have hg : 0 < g := by dsimp [g]; linarith
  let δ : ℝ := min (1 / 2) (min (η / (10 + 4 * C))
    (min (1 / (16 * (C + 1))) (g / (4 * (3 * C + 1)))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro ε hε0 hεδ
  have hehalf : ε < 1 / 2 := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hdiv1 : ε < η / (10 + 4 * C) :=
    lt_of_lt_of_le hεδ ((min_le_right _ _).trans (min_le_left _ _))
  have hdiv2 : ε < 1 / (16 * (C + 1)) :=
    lt_of_lt_of_le hεδ ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hdiv3 : ε < g / (4 * (3 * C + 1)) :=
    lt_of_lt_of_le hεδ ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hcover : (10 + 4 * C) * ε ≤ η := by
    have h := (lt_div_iff₀ (by positivity : 0 < 10 + 4 * C)).mp hdiv1
    nlinarith only [h]
  have he1 : ε ≤ 1 := by linarith only [hehalf]
  have he2 : ε ^ 2 ≤ 1 := by nlinarith only [hε0, he1]
  have hCE : C * ε ^ 2 ≤ 1 / 16 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 16 * (C + 1))).mp hdiv2
    have hm := mul_le_mul_of_nonneg_left he1 (mul_nonneg hC hε0.le)
    nlinarith only [h, hm, hε0]
  have hsaving : 2 * (3 * C + 1) * ε ^ 2 < g := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4 * (3 * C + 1))).mp hdiv3
    have hm := mul_le_mul_of_nonneg_left he1
      (show 0 ≤ (3 * C + 1) * ε by positivity)
    have hp : 0 ≤ (3 * C + 1) * ε := by positivity
    nlinarith only [h, hm, hp]
  exact ⟨hehalf.le, hcover, he2, hCE, hsaving⟩

end CylinderCovering.GeneralCapArea

end OAI
