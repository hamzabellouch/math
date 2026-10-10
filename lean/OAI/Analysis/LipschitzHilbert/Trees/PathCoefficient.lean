import OAI.Analysis.LipschitzHilbert.Trees.ComplementaryMass
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-!
# The dominant-path coefficient from complementary masses

For the path child in §9 the coefficient is
`l^(1-α/p) * r^μ`, where `l=nₐ/n` and `r=nₐ/mₐ`.
Its defect from one and its variation retain the relative path drop.
-/

noncomputable section

namespace LipschitzHilbert

def pathCoefficient (a b l r : ℝ) : ℝ := l ^ a * r ^ b

theorem pathCoefficient_pos {a b l r : ℝ} (hl : 0 < l) (hr : 0 < r) :
    0 < pathCoefficient a b l r := by
  unfold pathCoefficient
  positivity

theorem pathCoefficient_le_one {a b l r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    pathCoefficient a b l r ≤ 1 := by
  unfold pathCoefficient
  calc
    l ^ a * r ^ b ≤ 1 * r ^ b :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_one hl0 hl1 ha) (Real.rpow_nonneg hr0 _)
    _ ≤ 1 := by simpa only [one_mul] using Real.rpow_le_one hr0 hr1 hb

/-- Both mass fractions lie above `1-u`, so two exponents in `[0,1]`
give a coefficient defect at most `2u`. -/
theorem pathCoefficient_defect {a b l r u : ℝ}
    (ha : a ≤ 1) (hb : b ≤ 1) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hl : 1 - l ≤ u) (hr : 1 - r ≤ u) :
    1 - pathCoefficient a b l r ≤ 2 * u := by
  have hpowL := Real.self_le_rpow_of_le_one hl0 hl1 ha
  have hpowR := Real.self_le_rpow_of_le_one hr0 hr1 hb
  have hprod : l * r ≤ pathCoefficient a b l r := by
    exact mul_le_mul hpowL hpowR hr0 (Real.rpow_nonneg hl0 _)
  have hcompl := mul_nonneg (sub_nonneg.mpr hl1) (sub_nonneg.mpr hr1)
  nlinarith

/-- Exponentiation is one-Lipschitz on the nonpositive real half-line. -/
theorem exp_nonpositive_lipschitz {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  have h := (convex_Iic (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => Real.differentiableAt_exp)
    (fun x hx => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
      exact Real.exp_le_one_iff.mpr hx) hy hx
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem positive_unit_interval_motion {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    |x - y| ≤ |Real.log x - Real.log y| := by
  have h := exp_nonpositive_lipschitz (Real.log_nonpos hx0.le hx1) (Real.log_nonpos hy0.le hy1)
  simpa only [Real.exp_log hx0, Real.exp_log hy0] using h

/-- Variation of the coefficient is controlled by the two complementary-mass
logarithm variations, with the exact exponent weights. -/
theorem pathCoefficient_motion {a b l r l' r' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hl0 : 0 < l) (hl1 : l ≤ 1) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hl'0 : 0 < l') (hl'1 : l' ≤ 1) (hr'0 : 0 < r') (hr'1 : r' ≤ 1) :
    |pathCoefficient a b l' r' - pathCoefficient a b l r| ≤
      a * |Real.log l' - Real.log l| + b * |Real.log r' - Real.log r| := by
  have h := positive_unit_interval_motion (pathCoefficient_pos hl'0 hr'0)
    (pathCoefficient_le_one ha hb hl'0.le hl'1 hr'0.le hr'1)
    (pathCoefficient_pos hl0 hr0) (pathCoefficient_le_one ha hb hl0.le hl1 hr0.le hr1)
  have hlog (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
      Real.log (pathCoefficient a b x y) = a * Real.log x + b * Real.log y := by
    unfold pathCoefficient
    rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne' (Real.rpow_pos_of_pos hy _).ne',
      Real.log_rpow hx, Real.log_rpow hy]
  rw [hlog l' r' hl'0 hr'0, hlog l r hl0 hr0] at h
  refine h.trans ?_
  calc
    _ = |a * (Real.log l' - Real.log l) + b * (Real.log r' - Real.log r)| := by congr 1; ring
    _ ≤ |a * (Real.log l' - Real.log l)| + |b * (Real.log r' - Real.log r)| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- The actual shared child mass and its two complementary masses imply all
coefficient hypotheses used by the dominant prediction comparison. -/
theorem pathCoefficient_from_complementary_masses
    {a b n B D n' B' D' ε u : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hn : 0 < n) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hnmove : |n' - n| ≤ ε * n) (hBmove : |B' - B| ≤ ε * B)
    (hDmove : |D' - D| ≤ ε * D)
    (hBdrop : 1 - n / (n + B) ≤ u) (hDdrop : 1 - n / (n + D) ≤ u) :
    let C := pathCoefficient a b (n / (n + B)) (n / (n + D))
    let C' := pathCoefficient a b (n' / (n' + B')) (n' / (n' + D'))
    0 < C ∧ C ≤ 1 ∧ 1 - C ≤ 2 * u ∧ 0 < C' ∧ C' ≤ 1 ∧ |C' - C| ≤ 24 * ε * u := by
  dsimp only
  obtain ⟨hn', hnB', _⟩ := complementary_mass_fraction_motion hn hB hε0 hε1 hnmove hBmove
  obtain ⟨_, hnD', _⟩ := complementary_mass_fraction_motion hn hD hε0 hε1 hnmove hDmove
  have hB' : 0 ≤ B' := by
    have hmul := mul_le_mul_of_nonneg_right hε1 hB
    linarith [(abs_le.mp hBmove).1]
  have hD' : 0 ≤ D' := by
    have hmul := mul_le_mul_of_nonneg_right hε1 hD
    linarith [(abs_le.mp hDmove).1]
  have hl0 : 0 < n / (n + B) := div_pos hn (by linarith)
  have hr0 : 0 < n / (n + D) := div_pos hn (by linarith)
  have hl1 : n / (n + B) ≤ 1 := (div_le_one (by linarith : 0 < n + B)).2 (by linarith)
  have hr1 : n / (n + D) ≤ 1 := (div_le_one (by linarith : 0 < n + D)).2 (by linarith)
  have hl'0 : 0 < n' / (n' + B') := div_pos hn' hnB'
  have hr'0 : 0 < n' / (n' + D') := div_pos hn' hnD'
  have hl'1 : n' / (n' + B') ≤ 1 := (div_le_one hnB').2 (by linarith)
  have hr'1 : n' / (n' + D') ≤ 1 := (div_le_one hnD').2 (by linarith)
  refine ⟨pathCoefficient_pos hl0 hr0, pathCoefficient_le_one ha0 hb0 hl0.le hl1 hr0.le hr1,
    pathCoefficient_defect ha1 hb1 hl0.le hl1 hr0.le hr1 hBdrop hDdrop,
    pathCoefficient_pos hl'0 hr'0, pathCoefficient_le_one ha0 hb0 hl'0.le hl'1 hr'0.le hr'1, ?_⟩
  have hlmove := (complementary_mass_log_motion hn hB hε0 hε1 hnmove hBmove).trans
    (mul_le_mul_of_nonneg_left hBdrop (by positivity : 0 ≤ 12 * ε))
  have hrmove := (complementary_mass_log_motion hn hD hε0 hε1 hnmove hDmove).trans
    (mul_le_mul_of_nonneg_left hDdrop (by positivity : 0 ≤ 12 * ε))
  have h := pathCoefficient_motion ha0 hb0 hl0 hl1 hr0 hr1 hl'0 hl'1 hr'0 hr'1
  have hfirst := mul_le_mul_of_nonneg_left hlmove ha0
  have hsecond := mul_le_mul_of_nonneg_left hrmove hb0
  have hunitL := mul_le_mul_of_nonneg_right ha1 (abs_nonneg (Real.log (n' / (n' + B')) - Real.log (n / (n + B))))
  have hunitR := mul_le_mul_of_nonneg_right hb1 (abs_nonneg (Real.log (n' / (n' + D')) - Real.log (n / (n + D))))
  nlinarith

end LipschitzHilbert

end

end OAI
