import OAI.Geometry.RCD.Coordinates.WeightedFitSmoothing

namespace OAI

/-! # Summable squared radial errors from the actual contraction -/

namespace RegularPointCoordinates

/-- A weighted pointwise envelope bounds the total normalized squared
error by the total original defect and the qualitative error floor. -/
theorem normalized_squared_fit_budget {σ η A : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ < 1)
    (hη : 0 ≤ η) (hA : 0 ≤ A) {P e w : ℕ → ℝ}
    (hP : ∀ i, 0 ≤ P i) (hPs : Summable P) (hw : ∀ i, 0 < w i)
    (hbound : ∀ i, (e i) ^ 2 ≤ A * forwardDefect σ η P i * (w i) ^ 2) :
    Summable (fun i => (e i / w i) ^ 2) ∧
      (∑' i, (e i / w i) ^ 2) ≤ A * (1 - σ)⁻¹ * (η + ∑' i, P i) := by
  have hforward := forwardDefect_budget hσ hσ1 hη hP hPs
  have hp (i : ℕ) : (e i / w i) ^ 2 ≤ A * forwardDefect σ η P i := by
    rw [div_pow]
    exact (div_le_iff₀ (sq_pos_of_pos (hw i))).mpr (hbound i)
  have hs := Summable.of_nonneg_of_le (fun i => sq_nonneg (e i / w i)) hp
    (hforward.1.mul_left A)
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' i, A * forwardDefect σ η P i := hs.tsum_le_tsum hp (hforward.1.mul_left A)
    _ = A * ∑' i, forwardDefect σ η P i := tsum_mul_left
    _ ≤ A * ((1 - σ)⁻¹ * (η + ∑' i, P i)) := mul_le_mul_of_nonneg_left hforward.2 hA
    _ = _ := by ring

/-- The fixed harmonic contraction dominates the slow change of
covector norm. The coefficient is chosen before the defect sequence and
the size of the qualitative error. -/
theorem radial_fit_forward_envelope {m : ℕ} (hm : 0 < m) {C : ℝ} (hC : 0 ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ {η : ℝ}, 0 ≤ η → ∀ {P e w : ℕ → ℝ},
      (∀ i, 0 ≤ P i) → (∀ i, 0 ≤ e i) → (∀ i, 0 < w i) →
      (∀ i, (e i) ^ 2 ≤ η * (w i) ^ 2) →
      (∀ i, w i ≤ (9 / 8 : ℝ) ^ m * w (i + m)) →
      (∀ i, e (i + m) ≤ (1 / 2 : ℝ) * Real.sqrt ((1 / 2 : ℝ) ^ m) * e i +
        C * w i * Real.sqrt (P i)) →
      ∀ i, (e i) ^ 2 ≤ A * forwardDefect (3 / 4) η P i * (w i) ^ 2 := by
  let σ : ℝ := 3 / 4
  let θ : ℝ := (1 / 2 : ℝ) ^ m
  let a := (1 / 2 : ℝ) * Real.sqrt θ
  let G : ℝ := (9 / 8 : ℝ) ^ m
  let A := (2 + 4 * (C * G) ^ 2) / σ ^ m
  have hσ : 0 < σ := by norm_num [σ]
  have hσ1 : σ ≤ 1 := by norm_num [σ]
  have hθ : 0 ≤ θ := pow_nonneg (by norm_num) _
  have hG : 0 ≤ G := pow_nonneg (by norm_num) _
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  have hscale : A * σ ^ m = 2 + 4 * (C * G) ^ 2 :=
    div_mul_cancel₀ _ (pow_ne_zero _ hσ.ne')
  have hcontract : 2 * (a * G) ^ 2 ≤ (1 / 2 : ℝ) * σ ^ m := by
    have hp : (81 / 128 : ℝ) ^ m ≤ σ ^ m :=
      pow_le_pow_left₀ (by norm_num) (by norm_num [σ]) _
    have he : 2 * (a * G) ^ 2 = (1 / 2 : ℝ) * (81 / 128 : ℝ) ^ m := by
      dsimp only [a, G]
      rw [mul_pow, mul_pow, Real.sq_sqrt hθ]
      dsimp only [θ]
      rw [← pow_mul, Nat.mul_comm m 2, pow_mul]
      calc
        _ = (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ m * ((9 / 8 : ℝ) ^ 2) ^ m) := by ring
        _ = (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (9 / 8 : ℝ) ^ 2) ^ m := by rw [mul_pow]
        _ = _ := by norm_num
    rw [he]
    exact mul_le_mul_of_nonneg_left hp (by norm_num)
  have hmargin : (2 * (a * G) ^ 2) * A + 2 * (C * G) ^ 2 ≤ σ ^ m * A := by
    have hh := mul_le_mul_of_nonneg_right hcontract hA.le
    nlinarith [sq_nonneg (C * G)]
  refine ⟨A, hA, ?_⟩
  intro η hη P e w hP he hw hsmall hgrowth hstep
  apply weighted_squared_fit_le_forwardDefect hσ.le hη hA.le ha hC hG hP he hw hm hmargin
  · intro i hi
    have hratio : (e i / w i) ^ 2 ≤ η := by
      rw [div_pow]
      exact (div_le_iff₀ (sq_pos_of_pos (hw i))).mpr (hsmall i)
    have hp : σ ^ m ≤ σ ^ i := pow_le_pow_of_le_one hσ.le hσ1 hi.le
    have hAi : 1 ≤ A * σ ^ i := by
      have hh := mul_le_mul_of_nonneg_left hp hA.le
      nlinarith [sq_nonneg (C * G)]
    calc
      _ ≤ η := hratio
      _ ≤ A * (η * σ ^ i) := by nlinarith
  · exact hgrowth
  · exact hstep

end RegularPointCoordinates

end OAI
