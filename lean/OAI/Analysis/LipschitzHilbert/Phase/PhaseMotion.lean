import OAI.Analysis.LipschitzHilbert.Estimates.ExponentialVariation
import OAI.Analysis.LipschitzHilbert.Estimates.LogEnergy
import OAI.Analysis.LipschitzHilbert.Phase.DiagonalPhaseSelection
import OAI.Analysis.LipschitzHilbert.Phase.PredictionNormalization

namespace OAI

/-!
# Motion of diagonal Fourier predictions

Bounded frequencies give explicit Lipschitz bounds for the actual characters
and Hilbert-valued phase sums. Together with logarithmic energy control these
give the multiplicative cell-supremum bound required by §9.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
theorem character_motion (frequency s t : ℝ) :
    ‖character frequency t - character frequency s‖ ≤ |frequency| * |t - s| := by
  have h := norm_exp_sub_le_of_re_le
    (((frequency * s : ℝ) : ℂ) * Complex.I)
    (((frequency * t : ℝ) : ℂ) * Complex.I) 0 (by simp) (by simp)
  have hd : (((frequency * t : ℝ) : ℂ) * Complex.I) -
      (((frequency * s : ℝ) : ℂ) * Complex.I) =
      ((frequency * (t - s) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hd, Real.exp_zero, one_mul, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Real.norm_eq_abs, abs_mul] at h
  exact h

omit [Fintype ι] in
theorem diagonalModulation_motion (frequency : κ → ℝ) (a : EuclideanSpace ℂ κ)
    {L : ℝ} (hL : 0 ≤ L) (hfrequency : ∀ j, |frequency j| ≤ L) (s t : ℝ) :
    ‖diagonalModulation frequency a t - diagonalModulation frequency a s‖ ≤
      L * ‖a‖ * |t - s| := by
  have hcoordinate (j : κ) :
      ‖(diagonalModulation frequency a t - diagonalModulation frequency a s) j‖ ≤
        ‖a j‖ * (L * |t - s|) := by
    have heq : (diagonalModulation frequency a t - diagonalModulation frequency a s) j =
        a j * (character (frequency j) t - character (frequency j) s) := by
      simp only [PiLp.sub_apply, diagonalModulation]
      ring
    rw [heq, norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((character_motion (frequency j) s t).trans
        (mul_le_mul_of_nonneg_right (hfrequency j) (abs_nonneg _))) (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ L * ‖a‖ * |t - s|)).mp
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ j, (‖a j‖ * (L * |t - s|)) ^ 2 :=
      Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hcoordinate j) 2
    _ = (L * ‖a‖ * |t - s|) ^ 2 := by
      simp_rw [mul_pow]
      rw [← Finset.sum_mul, ← EuclideanSpace.norm_sq_eq]
      ring

/-- Uniform frequency control bounds the motion by the total coefficient norm. -/
theorem diagonalFourierSum_motion (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) {L : ℝ} (hL : 0 ≤ L)
    (hfrequency : ∀ i j, |frequency i j| ≤ L) (s t : ℝ) :
    ‖diagonalFourierSum frequency a t - diagonalFourierSum frequency a s‖ ≤
      L * (∑ i, ‖a i‖) * |t - s| := by
  rw [diagonalFourierSum_eq_sum, diagonalFourierSum_eq_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖diagonalModulation (frequency i) (a i) t -
        diagonalModulation (frequency i) (a i) s‖ := norm_sum_le _ _
    _ ≤ ∑ i, L * ‖a i‖ * |t - s| := Finset.sum_le_sum fun i _ =>
      diagonalModulation_motion (frequency i) (a i) hL (hfrequency i) s t
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- The fixed positive denominator disappears from logarithmic motion. -/
theorem diagonal_prediction_log_motion (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) {L p denominator : ℝ}
    (hL : 0 ≤ L) (hp : 1 ≤ p) (hd : 0 < denominator)
    (hfrequency : ∀ i j, |frequency i j| ≤ L) (s t : ℝ) :
    |Real.log (energyRatio p denominator (diagonalFourierSum frequency a t)) -
      Real.log (energyRatio p denominator (diagonalFourierSum frequency a s))| ≤
        p * L * (∑ i, ‖a i‖) * |t - s| := by
  calc
    _ ≤ p * ‖diagonalFourierSum frequency a t - diagonalFourierSum frequency a s‖ :=
      log_energyRatio_lipschitz hp hd _ _
    _ ≤ p * (L * (∑ i, ‖a i‖) * |t - s|) :=
      mul_le_mul_of_nonneg_left (diagonalFourierSum_motion frequency a hL hfrequency s t)
        (by linarith)
    _ = _ := by ring

/-- The actual Fourier prediction, maximized on a cell of bounded diameter,
differs from its value by the stated exponential factor. -/
theorem diagonal_prediction_cell_sup (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (I : Set ℝ) {s L p denominator H : ℝ}
    (hs : s ∈ I) (hL : 0 ≤ L) (hp : 1 ≤ p) (hd : 0 < denominator)
    (hfrequency : ∀ i j, |frequency i j| ≤ L)
    (hdiameter : ∀ t ∈ I, |t - s| ≤ H) :
    energyRatio p denominator (diagonalFourierSum frequency a s) ≤
      predictionCellSup (fun t => energyRatio p denominator (diagonalFourierSum frequency a t)) I ∧
    predictionCellSup (fun t => energyRatio p denominator (diagonalFourierSum frequency a t)) I ≤
      Real.exp (p * L * (∑ i, ‖a i‖) * H) *
        energyRatio p denominator (diagonalFourierSum frequency a s) := by
  apply prediction_cell_sup_bounds _ I hs (fun t _ => energyRatio_pos hd _)
  intro t ht
  exact (diagonal_prediction_log_motion frequency a hL hp hd hfrequency s t).trans
    (mul_le_mul_of_nonneg_left (hdiameter t ht) (by positivity))

/-- Removing the path carrier leaves a fixed vector. Its size does not enter
logarithmic motion; only the off-path Fourier coefficients contribute. -/
theorem fixed_path_diagonal_log_motion (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (Y : EuclideanSpace ℂ κ)
    {L p denominator : ℝ} (hL : 0 ≤ L) (hp : 1 ≤ p) (hd : 0 < denominator)
    (hfrequency : ∀ i j, |frequency i j| ≤ L) (s t : ℝ) :
    |Real.log (energyRatio p denominator (Y + diagonalFourierSum frequency a t)) -
      Real.log (energyRatio p denominator (Y + diagonalFourierSum frequency a s))| ≤
        p * L * (∑ i, ‖a i‖) * |t - s| := by
  have h := log_energyRatio_lipschitz hp hd (Y + diagonalFourierSum frequency a t)
    (Y + diagonalFourierSum frequency a s)
  rw [add_sub_add_left_eq_sub] at h
  refine h.trans ?_
  have hm := mul_le_mul_of_nonneg_left
    (diagonalFourierSum_motion frequency a hL hfrequency s t) (show 0 ≤ p by linarith)
  convert hm using 1
  ring

/-- The source's small-drop form of step supremum control: when the off-path
coefficient mass is at most `K*u`, the exponent retains the factor `u`. -/
theorem fixed_path_diagonal_cell_sup (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (Y : EuclideanSpace ℂ κ) (I : Set ℝ)
    {s L p denominator H K u : ℝ} (hs : s ∈ I)
    (hL : 0 ≤ L) (hp : 1 ≤ p) (hd : 0 < denominator) (hH : 0 ≤ H)
    (hfrequency : ∀ i j, |frequency i j| ≤ L)
    (hdiameter : ∀ t ∈ I, |t - s| ≤ H) (hmass : ∑ i, ‖a i‖ ≤ K * u) :
    energyRatio p denominator (Y + diagonalFourierSum frequency a s) ≤
      predictionCellSup (fun t => energyRatio p denominator (Y + diagonalFourierSum frequency a t)) I ∧
    predictionCellSup (fun t => energyRatio p denominator (Y + diagonalFourierSum frequency a t)) I ≤
      Real.exp ((p * L * K * H) * u) *
        energyRatio p denominator (Y + diagonalFourierSum frequency a s) := by
  apply prediction_cell_sup_bounds _ I hs (fun t _ => energyRatio_pos hd _)
  intro t ht
  calc
    _ ≤ p * L * (∑ i, ‖a i‖) * |t - s| :=
      fixed_path_diagonal_log_motion frequency a Y hL hp hd hfrequency s t
    _ ≤ p * L * (∑ i, ‖a i‖) * H :=
      mul_le_mul_of_nonneg_left (hdiameter t ht) (by positivity)
    _ ≤ p * L * (K * u) * H :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by positivity)) hH
    _ = (p * L * K * H) * u := by ring

omit [Fintype ι] [Fintype κ] in
/-- Blending a positive prediction with one contracts its logarithmic
oscillation. This proves the blend step without differentiating the ratio. -/
theorem blend_log_contraction {θ x y : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hx : 0 < x) (hy : 0 < y) :
    |Real.log ((1 - θ) * x + θ) - Real.log ((1 - θ) * y + θ)| ≤
      |Real.log x - Real.log y| := by
  let d := |Real.log x - Real.log y|
  have hpos (z : ℝ) (hz : 0 < z) : 0 < (1 - θ) * z + θ := by
    by_cases hθ : θ = 1
    · simp [hθ]
    · have hfactor : 0 < 1 - θ := sub_pos.mpr (lt_of_le_of_ne hθ1 hθ)
      exact add_pos_of_pos_of_nonneg (mul_pos hfactor hz) hθ0
  have hscale (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
      (hab : Real.log a - Real.log b ≤ d) : a ≤ Real.exp d * b := by
    calc
      a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ ≤ Real.exp (d + Real.log b) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_add, Real.exp_log hb]
  have hxy : x ≤ Real.exp d * y := hscale x y hx hy (le_abs_self _)
  have hyx : y ≤ Real.exp d * x := hscale y x hy hx (by
    dsimp [d]
    rw [abs_sub_comm]
    exact le_abs_self _)
  have hexp : 1 ≤ Real.exp d := Real.one_le_exp (abs_nonneg _)
  have hblend (a b : ℝ) (hab : a ≤ Real.exp d * b) :
      (1 - θ) * a + θ ≤ Real.exp d * ((1 - θ) * b + θ) := by
    have h₁ := mul_le_mul_of_nonneg_left hab (sub_nonneg.mpr hθ1)
    have h₂ := mul_le_mul_of_nonneg_right hexp hθ0
    nlinarith
  have hlogxy : Real.log ((1 - θ) * x + θ) ≤ d + Real.log ((1 - θ) * y + θ) := by
    apply (Real.log_le_iff_le_exp (hpos x hx)).2
    rw [Real.exp_add, Real.exp_log (hpos y hy)]
    exact hblend x y hxy
  have hlogyx : Real.log ((1 - θ) * y + θ) ≤ d + Real.log ((1 - θ) * x + θ) := by
    apply (Real.log_le_iff_le_exp (hpos y hy)).2
    rw [Real.exp_add, Real.exp_log (hpos x hx)]
    exact hblend y x hyx
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- The source's final blended prediction obeys the same relative-drop
cell supremum bound as its unblended model. -/
theorem fixed_path_blended_cell_sup (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (Y : EuclideanSpace ℂ κ) (I : Set ℝ)
    {s L p denominator H K u θ : ℝ} (hs : s ∈ I)
    (hL : 0 ≤ L) (hp : 1 ≤ p) (hd : 0 < denominator) (hH : 0 ≤ H)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hfrequency : ∀ i j, |frequency i j| ≤ L)
    (hdiameter : ∀ t ∈ I, |t - s| ≤ H) (hmass : ∑ i, ‖a i‖ ≤ K * u) :
    let B := fun t => (1 - θ) * energyRatio p denominator (Y + diagonalFourierSum frequency a t) + θ
    B s ≤ predictionCellSup B I ∧
      predictionCellSup B I ≤ Real.exp ((p * L * K * H) * u) * B s := by
  dsimp only
  apply prediction_cell_sup_bounds _ I hs
  · intro t _
    have hz := energyRatio_pos hd (Y + diagonalFourierSum frequency a t) (p := p)
    by_cases hθ : θ = 1
    · simp [hθ]
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr (lt_of_le_of_ne hθ1 hθ)) hz) hθ0
  · intro t ht
    refine (blend_log_contraction hθ0 hθ1 (energyRatio_pos hd _) (energyRatio_pos hd _)).trans ?_
    calc
      _ ≤ p * L * (∑ i, ‖a i‖) * |t - s| :=
        fixed_path_diagonal_log_motion frequency a Y hL hp hd hfrequency s t
      _ ≤ p * L * (∑ i, ‖a i‖) * H :=
        mul_le_mul_of_nonneg_left (hdiameter t ht) (by positivity)
      _ ≤ p * L * (K * u) * H :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by positivity)) hH
      _ = _ := by ring

end LipschitzHilbert

end

end OAI
