import OAI.Probability.SLE.Geometry.CurveJoin
import OAI.Probability.SLE.Gauge.SerpentineLayout

namespace OAI

/-! Unit-speed straight and semicircular pieces in ribbon-width units.
Their tangents match at each join and have the uniform Lipschitz bound
1/50 required by the fixed local ribbon constants. -/

noncomputable section
open Set Metric
open scoped NNReal

namespace SLEExactGauge.Serpentine

def straightPiece (m j : ℕ) (t : ℝ) : ℂ :=
  ((-100 * (m : ℝ) + 100 * j : ℝ) : ℂ) +
    ((side j * (-100 * (m : ℝ) + t) : ℝ) : ℂ) * Complex.I

def straightTangent (j : ℕ) : ℂ := (side j : ℂ) * Complex.I

def circularPiece (m j : ℕ) (t : ℝ) : ℂ :=
  ((-100 * (m : ℝ) + 100 * j + 50 - 50 * Real.cos (t / 50) : ℝ) : ℂ) +
    ((side j * (100 * (m : ℝ) + 50 * Real.sin (t / 50)) : ℝ) : ℂ) * Complex.I

def circularTangent (j : ℕ) (t : ℝ) : ℂ :=
  (Real.sin (t / 50) : ℂ) + ((side j * Real.cos (t / 50) : ℝ) : ℂ) * Complex.I

lemma straightPiece_hasDerivAt (m j : ℕ) (t : ℝ) :
    HasDerivAt (straightPiece m j) (straightTangent j) t := by
  have hd := (((hasDerivAt_id t).const_add (-100 * (m : ℝ))).const_mul (side j)).ofReal_comp
  convert (hd.mul_const Complex.I).const_add (((-100 * (m : ℝ) + 100 * j : ℝ) : ℂ)) using 1 <;> try rfl
  simp only [straightTangent, mul_one]

lemma circularPiece_hasDerivAt (m j : ℕ) (t : ℝ) :
    HasDerivAt (circularPiece m j) (circularTangent j t) t := by
  have ht : HasDerivAt (fun u : ℝ => u / 50) (1 / 50) t :=
    (hasDerivAt_id t).div_const 50
  have hx := (ht.cos.const_mul 50).const_sub (-100 * (m : ℝ) + 100 * j + 50)
  have hy := ((ht.sin.const_mul 50).const_add (100 * (m : ℝ))).const_mul (side j)
  convert hx.ofReal_comp.add (hy.ofReal_comp.mul_const Complex.I) using 1 <;> try rfl
  all_goals simp only [circularTangent]
  all_goals push_cast
  all_goals ring

lemma straightTangent_norm (j : ℕ) : ‖straightTangent j‖ = 1 := by
  simp only [straightTangent, norm_mul, Complex.norm_real, Real.norm_eq_abs, side_abs,
    Complex.norm_I, mul_one]

lemma circularTangent_norm (j : ℕ) (t : ℝ) : ‖circularTangent j t‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [circularTangent, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, mul_one, zero_add]
  calc
    _ = Real.sin (t / 50) ^ 2 + side j ^ 2 * Real.cos (t / 50) ^ 2 := by ring
    _ = 1 ^ 2 := by rw [side_sq, one_mul]; nlinarith [Real.sin_sq_add_cos_sq (t / 50)]

lemma circularTangent_hasDerivAt (j : ℕ) (t : ℝ) :
    HasDerivAt (circularTangent j)
      (((Real.cos (t / 50) / 50 : ℝ) : ℂ) - ((side j * Real.sin (t / 50) / 50 : ℝ) : ℂ) * Complex.I) t := by
  have ht : HasDerivAt (fun u : ℝ => u / 50) (1 / 50) t :=
    (hasDerivAt_id t).div_const 50
  convert ht.sin.ofReal_comp.add ((ht.cos.const_mul (side j)).ofReal_comp.mul_const Complex.I)
    using 1 <;> try rfl
  all_goals push_cast
  all_goals ring

lemma circularTangent_deriv_norm (j : ℕ) (t : ℝ) :
    ‖((Real.cos (t / 50) / 50 : ℝ) : ℂ) -
      ((side j * Real.sin (t / 50) / 50 : ℝ) : ℂ) * Complex.I‖ = (1 / 50 : ℝ) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 50)).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, zero_sub, mul_one, add_zero]
  calc
    _ = (Real.cos (t / 50) ^ 2 + side j ^ 2 * Real.sin (t / 50) ^ 2) / 50 ^ 2 := by ring
    _ = (1 / 50 : ℝ) ^ 2 := by
      rw [side_sq, one_mul]
      nlinarith [Real.sin_sq_add_cos_sq (t / 50)]

lemma circularTangent_lipschitz (j : ℕ) : LipschitzWith (1 / 50) (circularTangent j) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (circularTangent_hasDerivAt j t).differentiableAt)
  intro t
  rw [(circularTangent_hasDerivAt j t).deriv]
  exact_mod_cast (circularTangent_deriv_norm j t).le

lemma straight_circular_position_match (m j : ℕ) :
    straightPiece m j (200 * m) = circularPiece m j 0 := by
  apply Complex.ext
  · simp [straightPiece, circularPiece]
  · simp only [straightPiece, circularPiece, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      mul_zero, mul_one, add_zero, zero_add, zero_div, Real.sin_zero]
    ring

lemma circular_straight_position_match (m j : ℕ) :
    circularPiece m j (50 * Real.pi) = straightPiece m (j + 1) 0 := by
  apply Complex.ext
  · simp [straightPiece, circularPiece, side_succ]
    ring
  · simp [straightPiece, circularPiece, side_succ]

lemma straight_circular_tangent_match (j : ℕ) :
    straightTangent j = circularTangent j 0 := by simp [straightTangent, circularTangent]

lemma circular_straight_tangent_match (j : ℕ) :
    circularTangent j (50 * Real.pi) = straightTangent (j + 1) := by
  simp [straightTangent, circularTangent, side_succ]

end SLEExactGauge.Serpentine

end

end OAI
