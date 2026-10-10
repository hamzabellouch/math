import OAI.Probability.InvariantIsing.Magnetic.MagneticCurvatureBound

namespace OAI

/-! Centered bounded-spin moments used to control the coefficients of the
inverse-mean diffusion. These estimates apply to the actual tilted Gaussian
law, including zero covariance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

private lemma magnetic_bounded_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)

lemma magnetic_spin_mean_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : ∀ x, |M x| ≤ 1) : |∫ x, M x ∂μ| ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := M) (C := 1)
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hM x)
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h

lemma magnetic_centered_spin_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : ∀ x, |M x| ≤ 1) (x : ℝ) :
    |M x - ∫ y, M y ∂μ| ≤ 2 := by
  exact (abs_sub _ _).trans (by linarith [hM x, magnetic_spin_mean_bound μ hM])

lemma magnetic_centered_power_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) (k : ℕ) :
    Integrable (fun x => (M x - ∫ y, M y ∂μ) ^ k) μ := by
  apply magnetic_bounded_integrable μ ((hM.sub measurable_const).pow_const k)
  intro x
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (magnetic_centered_spin_bound μ bM x) k

lemma magnetic_centered_second (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) :
    (∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ) =
      (∫ x, (M x) ^ 2 ∂μ) - (∫ x, M x ∂μ) ^ 2 := by
  have h1 := magnetic_bounded_integrable μ hM bM
  have h2 : Integrable (fun x => (M x) ^ 2) μ :=
    magnetic_bounded_integrable μ (C := 1) (hM.pow_const 2) (fun x => by
      rw [abs_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (bM x) 2)
  let m := ∫ x, M x ∂μ
  calc
    _ = ∫ x, ((M x) ^ 2 - (2 * m) * M x) + m ^ 2 ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only [m]; ring
    _ = _ := by
      rw [integral_add (f := fun x => (M x) ^ 2 - (2 * m) * M x)
          (g := fun _ => m ^ 2) (h2.sub (h1.const_mul _)) (integrable_const _),
        integral_sub (f := fun x => (M x) ^ 2) (g := fun x => (2 * m) * M x)
          h2 (h1.const_mul _), integral_const_mul, integral_const]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      dsimp only [m]
      ring

lemma magnetic_centered_second_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) :
    0 ≤ (∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ) ∧
      (∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ) ≤ 1 := by
  constructor
  · exact integral_nonneg fun _ => sq_nonneg _
  · rw [magnetic_centered_second μ hM bM]
    have hi := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun x => (M x) ^ 2) (C := 1) (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (bM x) 2)
    simp only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at hi
    linarith [le_abs_self (∫ x, (M x) ^ 2 ∂μ), sq_nonneg (∫ x, M x ∂μ)]

lemma magnetic_centered_third (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) :
    (∫ x, (M x - ∫ y, M y ∂μ) ^ 3 ∂μ) =
      (∫ x, (M x) ^ 3 ∂μ) - 3 * (∫ x, M x ∂μ) * (∫ x, (M x) ^ 2 ∂μ) +
        2 * (∫ x, M x ∂μ) ^ 3 := by
  have hp (k : ℕ) : Integrable (fun x => (M x) ^ k) μ :=
    magnetic_bounded_integrable μ (C := 1) (hM.pow_const k) (fun x => by
      rw [abs_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (bM x) k)
  have h1 := magnetic_bounded_integrable μ hM bM
  let m := ∫ x, M x ∂μ
  calc
    _ = ∫ x, (((M x) ^ 3 - (3 * m) * (M x) ^ 2) + (3 * m ^ 2) * M x) - m ^ 3 ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only [m]; ring
    _ = _ := by
      rw [integral_sub (f := fun x => ((M x) ^ 3 - (3 * m) * (M x) ^ 2) + (3 * m ^ 2) * M x)
          (g := fun _ => m ^ 3) (((hp 3).sub ((hp 2).const_mul _)).add (h1.const_mul _))
          (integrable_const _),
        integral_add (f := fun x => (M x) ^ 3 - (3 * m) * (M x) ^ 2)
          (g := fun x => (3 * m ^ 2) * M x) ((hp 3).sub ((hp 2).const_mul _)) (h1.const_mul _),
        integral_sub (f := fun x => (M x) ^ 3) (g := fun x => (3 * m) * (M x) ^ 2)
          (hp 3) ((hp 2).const_mul _), integral_const_mul,
        integral_const_mul, integral_const]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      dsimp only [m]
      ring

lemma magnetic_centered_fourth (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) :
    (∫ x, (M x - ∫ y, M y ∂μ) ^ 4 ∂μ) =
      (∫ x, (M x) ^ 4 ∂μ) - 4 * (∫ x, M x ∂μ) * (∫ x, (M x) ^ 3 ∂μ) +
        6 * (∫ x, M x ∂μ) ^ 2 * (∫ x, (M x) ^ 2 ∂μ) -
        3 * (∫ x, M x ∂μ) ^ 4 := by
  have hp (k : ℕ) : Integrable (fun x => (M x) ^ k) μ :=
    magnetic_bounded_integrable μ (C := 1) (hM.pow_const k) (fun x => by
      rw [abs_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (bM x) k)
  have h1 := magnetic_bounded_integrable μ hM bM
  let m := ∫ x, M x ∂μ
  calc
    _ = ∫ x, ((((M x) ^ 4 - (4 * m) * (M x) ^ 3) + (6 * m ^ 2) * (M x) ^ 2) -
        (4 * m ^ 3) * M x) + m ^ 4 ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only [m]; ring
    _ = _ := by
      rw [integral_add
          (f := fun x => (((M x) ^ 4 - (4 * m) * (M x) ^ 3) + (6 * m ^ 2) * (M x) ^ 2) - (4 * m ^ 3) * M x)
          (g := fun _ => m ^ 4)
          ((((hp 4).sub ((hp 3).const_mul _)).add ((hp 2).const_mul _)).sub (h1.const_mul _))
          (integrable_const _),
        integral_sub (f := fun x => ((M x) ^ 4 - (4 * m) * (M x) ^ 3) + (6 * m ^ 2) * (M x) ^ 2)
          (g := fun x => (4 * m ^ 3) * M x)
          (((hp 4).sub ((hp 3).const_mul _)).add ((hp 2).const_mul _)) (h1.const_mul _),
        integral_add (f := fun x => (M x) ^ 4 - (4 * m) * (M x) ^ 3)
          (g := fun x => (6 * m ^ 2) * (M x) ^ 2)
          ((hp 4).sub ((hp 3).const_mul _)) ((hp 2).const_mul _),
        integral_sub (f := fun x => (M x) ^ 4) (g := fun x => (4 * m) * (M x) ^ 3)
          (hp 4) ((hp 3).const_mul _), integral_const_mul,
        integral_const_mul, integral_const_mul, integral_const]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      dsimp only [m]
      ring

lemma magnetic_weighted_centered_second (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M Q : ℝ → ℝ} (hM : Measurable M) (hQ : Measurable Q)
    (bM : ∀ x, |M x| ≤ 1) {C : ℝ} (bQ : ∀ x, |Q x| ≤ C) :
    (∫ x, Q x * (M x - ∫ y, M y ∂μ) ^ 2 ∂μ) =
      (∫ x, Q x * (M x) ^ 2 ∂μ) -
        2 * (∫ x, M x ∂μ) * (∫ x, Q x * M x ∂μ) +
        (∫ x, M x ∂μ) ^ 2 * (∫ x, Q x ∂μ) := by
  have hiQ := magnetic_bounded_integrable μ hQ bQ
  have hiQM (k : ℕ) : Integrable (fun x => Q x * (M x) ^ k) μ :=
    hiQ.mul_bdd (hM.pow_const k).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (bM x) k)
  let m := ∫ x, M x ∂μ
  calc
    _ = ∫ x, (Q x * (M x) ^ 2 - (2 * m) * (Q x * (M x) ^ 1)) +
        m ^ 2 * Q x ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only [m]; ring
    _ = _ := by
      rw [integral_add (f := fun x => Q x * (M x) ^ 2 - (2 * m) * (Q x * (M x) ^ 1))
          (g := fun x => m ^ 2 * Q x) ((hiQM 2).sub ((hiQM 1).const_mul _)) (hiQ.const_mul _),
        integral_sub (f := fun x => Q x * (M x) ^ 2) (g := fun x => (2 * m) * (Q x * (M x) ^ 1))
          (hiQM 2) ((hiQM 1).const_mul _), integral_const_mul,
        integral_const_mul]
      simp only [pow_one]
      dsimp only [m]

lemma magnetic_centered_third_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) :
    |∫ x, (M x - ∫ y, M y ∂μ) ^ 3 ∂μ| ≤
      2 * ∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ := by
  have h3 := magnetic_centered_power_integrable μ hM bM 3
  have h2 := magnetic_centered_power_integrable μ hM bM 2
  calc
    _ ≤ ∫ x, |(M x - ∫ y, M y ∂μ) ^ 3| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, 2 * (M x - ∫ y, M y ∂μ) ^ 2 ∂μ := by
      apply integral_mono h3.abs (h2.const_mul 2)
      intro x
      change |(M x - ∫ y, M y ∂μ) ^ 3| ≤ 2 * (M x - ∫ y, M y ∂μ) ^ 2
      rw [abs_pow, pow_succ _ 2]
      have hp := mul_le_mul_of_nonneg_left (magnetic_centered_spin_bound μ bM x)
        (sq_nonneg |M x - ∫ y, M y ∂μ|)
      nlinarith [sq_abs (M x - ∫ y, M y ∂μ)]
    _ = _ := integral_const_mul _ _

lemma magnetic_centered_fourth_cumulant_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) :
    |(∫ x, (M x - ∫ y, M y ∂μ) ^ 4 ∂μ) -
        3 * (∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ) ^ 2| ≤
      7 * ∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ := by
  let V := ∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ
  have hV := magnetic_centered_second_bounds μ hM bM
  have h4 : (∫ x, (M x - ∫ y, M y ∂μ) ^ 4 ∂μ) ≤ 4 * V := by
    calc
      _ ≤ ∫ x, 4 * (M x - ∫ y, M y ∂μ) ^ 2 ∂μ := by
        apply integral_mono (magnetic_centered_power_integrable μ hM bM 4)
          ((magnetic_centered_power_integrable μ hM bM 2).const_mul 4)
        intro x
        have hs := pow_le_pow_left₀ (abs_nonneg _) (magnetic_centered_spin_bound μ bM x) 2
        rw [sq_abs] at hs
        nlinarith [sq_nonneg (M x - ∫ y, M y ∂μ),
          mul_nonneg (sq_nonneg (M x - ∫ y, M y ∂μ)) (sub_nonneg.mpr hs)]
      _ = _ := integral_const_mul _ _
  have h4pos : 0 ≤ ∫ x, (M x - ∫ y, M y ∂μ) ^ 4 ∂μ :=
    integral_nonneg fun _ => by positivity
  calc
    _ ≤ |∫ x, (M x - ∫ y, M y ∂μ) ^ 4 ∂μ| + |3 * V ^ 2| := abs_sub _ _
    _ = (∫ x, (M x - ∫ y, M y ∂μ) ^ 4 ∂μ) + 3 * V ^ 2 := by
      rw [abs_of_nonneg h4pos, abs_of_nonneg (by positivity)]
    _ ≤ 7 * V := by dsimp only [V] at *; nlinarith

lemma magnetic_weighted_centered_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M Q : ℝ → ℝ} (hM : Measurable M) (hQ : Measurable Q)
    (bM : ∀ x, |M x| ≤ 1) {C : ℝ} (bQ : ∀ x, |Q x| ≤ C)
    (hQpos : ∀ x, 0 ≤ Q x) :
    |(∫ x, Q x * M x ∂μ) - (∫ x, Q x ∂μ) * (∫ x, M x ∂μ)| ≤
      2 * ∫ x, Q x ∂μ := by
  let m := ∫ x, M x ∂μ
  have hi := magnetic_bounded_integrable μ hQ bQ
  have hip : Integrable (fun x => Q x * M x) μ :=
    magnetic_bounded_integrable μ (hQ.mul hM) (fun x => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (bM x) (abs_nonneg _)).trans (by simpa using bQ x))
  have hic : Integrable (fun x => Q x * (M x - m)) μ := by
    convert hip.sub (hi.mul_const m) using 1
    funext x
    change Q x * (M x - m) = Q x * M x - Q x * m
    ring
  have he : (∫ x, Q x * M x ∂μ) - (∫ x, Q x ∂μ) * m =
      ∫ x, Q x * (M x - m) ∂μ := by
    rw [show (fun x => Q x * (M x - m)) = fun x => Q x * M x - Q x * m by
      funext x; ring, integral_sub hip (hi.mul_const m), integral_mul_const]
  change |(∫ x, Q x * M x ∂μ) - (∫ x, Q x ∂μ) * m| ≤ _
  rw [he]
  calc
    _ ≤ ∫ x, |Q x * (M x - m)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, 2 * Q x ∂μ := by
      apply integral_mono hic.abs (hi.const_mul 2)
      intro x
      change |Q x * (M x - m)| ≤ 2 * Q x
      rw [abs_mul, abs_of_nonneg (hQpos x)]
      have hb := mul_le_mul_of_nonneg_left (magnetic_centered_spin_bound μ bM x) (hQpos x)
      dsimp only [m]
      linarith
    _ = _ := integral_const_mul _ _

lemma magnetic_nonnegative_spin_variance_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {Q : ℝ → ℝ} (hQ : Measurable Q) (hQpos : ∀ x, 0 ≤ Q x) (hQle : ∀ x, Q x ≤ 1) :
    0 ≤ (∫ x, (Q x) ^ 2 ∂μ) - (∫ x, Q x ∂μ) ^ 2 ∧
      (∫ x, (Q x) ^ 2 ∂μ) - (∫ x, Q x ∂μ) ^ 2 ≤ ∫ x, Q x ∂μ := by
  have bQ : ∀ x, |Q x| ≤ 1 := fun x => by rw [abs_of_nonneg (hQpos x)]; exact hQle x
  have hiQ := magnetic_bounded_integrable μ hQ bQ
  have hiQ2 : Integrable (fun x => (Q x) ^ 2) μ :=
    magnetic_bounded_integrable μ (C := 1) (hQ.pow_const 2) (fun x => by
      rw [abs_pow]; simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (bQ x) 2)
  constructor
  · rw [← magnetic_centered_second μ hQ bQ]
    exact integral_nonneg fun _ => sq_nonneg _
  · have hle : (∫ x, (Q x) ^ 2 ∂μ) ≤ ∫ x, Q x ∂μ :=
      integral_mono hiQ2 hiQ (fun x => by nlinarith [hQpos x, hQle x])
    linarith [sq_nonneg (∫ x, Q x ∂μ)]

lemma magnetic_weighted_variance_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M Q : ℝ → ℝ} (hM : Measurable M) (hQ : Measurable Q)
    (bM : ∀ x, |M x| ≤ 1) {C : ℝ} (bQ : ∀ x, |Q x| ≤ C)
    (hQpos : ∀ x, 0 ≤ Q x) :
    |(∫ x, Q x * (M x - ∫ y, M y ∂μ) ^ 2 ∂μ) -
      (∫ x, Q x ∂μ) * (∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ)| ≤
      5 * ∫ x, Q x ∂μ := by
  let m := ∫ x, M x ∂μ
  let q := ∫ x, Q x ∂μ
  let V := ∫ x, (M x - m) ^ 2 ∂μ
  have hq : 0 ≤ q := integral_nonneg hQpos
  have hV := magnetic_centered_second_bounds μ hM bM
  have hiQ := magnetic_bounded_integrable μ hQ bQ
  have hib : ∀ x, |Q x * (M x - m) ^ 2| ≤ C * 4 := by
    intro x
    rw [abs_mul, abs_pow]
    have hc : 0 ≤ C := (abs_nonneg _).trans (bQ 0)
    have hs := pow_le_pow_left₀ (abs_nonneg _) (magnetic_centered_spin_bound μ bM x) 2
    exact mul_le_mul (bQ x) (by change |M x - ∫ y, M y ∂μ| ^ 2 ≤ 4; exact hs.trans_eq (by norm_num)) (by positivity) hc
  have hi : Integrable (fun x => Q x * (M x - m) ^ 2) μ :=
    magnetic_bounded_integrable μ (hQ.mul ((hM.sub measurable_const).pow_const 2)) hib
  have hip : 0 ≤ ∫ x, Q x * (M x - m) ^ 2 ∂μ :=
    integral_nonneg fun x => mul_nonneg (hQpos x) (sq_nonneg _)
  have hi4 : (∫ x, Q x * (M x - m) ^ 2 ∂μ) ≤ 4 * q := by
    calc
      _ ≤ ∫ x, 4 * Q x ∂μ := by
        apply integral_mono hi (hiQ.const_mul 4)
        intro x
        have hs := pow_le_pow_left₀ (abs_nonneg _) (magnetic_centered_spin_bound μ bM x) 2
        rw [sq_abs] at hs
        dsimp only [m]
        nlinarith [mul_nonneg (hQpos x) (sub_nonneg.mpr hs)]
      _ = _ := integral_const_mul _ _
  change |(∫ x, Q x * (M x - m) ^ 2 ∂μ) - q * V| ≤ 5 * q
  calc
    _ ≤ |∫ x, Q x * (M x - m) ^ 2 ∂μ| + |q * V| := abs_sub _ _
    _ = (∫ x, Q x * (M x - m) ^ 2 ∂μ) + q * V := by
      rw [abs_of_nonneg hip, abs_of_nonneg (mul_nonneg hq hV.1)]
    _ ≤ _ := by nlinarith [mul_nonneg hq (sub_nonneg.mpr hV.2)]

end InvariantIsing

end

end OAI
