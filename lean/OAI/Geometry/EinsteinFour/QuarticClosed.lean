import OAI.Geometry.EinsteinFour.QuarticEnergy

namespace OAI

/-! The quartic estimate at vanishing Weyl blocks, with totalized division. -/

namespace PositiveEinsteinFour.QuarticClosed

open Energy QuarticEnergy

noncomputable section

/-- The surviving part of (19) when the first block and its energy vanish.
This expression has no division by the norm of that vanished block. -/
def axisEnergy (x b τ χ d f : ℝ) : ℝ :=
  (1 / 2) * Real.sqrt (3 / 5) * gradientSum 0 ((5 / 3) * d) *
    (scalarWeight b x * (f * Real.sqrt f)) +
    (9 / 64) * (gradientSum 0 ((5 / 3) * d)) ^ 2 *
      (projectionCoefficient b x τ χ * ((5 / 3) * d) +
        defectCoefficient b x * (f - (5 / 3) * d)) -
    (17 / 10) * f * ((f - (3 / 5) * ((5 / 3) * d)) / b)

/-- Cancellation at a vanished first block is exact under Lean's totalized
field division, including at zero norm. -/
theorem quarticEnergy_axis (x b τ χ d f g H : ℝ) :
    quarticEnergy x b 0 ((5 / 3) * d) g (projectionCoefficient b x τ χ)
      H (defectCoefficient b x) 0 f = axisEnergy x b τ χ d f := by
  unfold quarticEnergy axisEnergy
  simp only [Real.sqrt_zero, mul_zero, add_zero, zero_add, sub_zero,
    zero_div]

/-- The quartic bound on a single surviving block. A continuous approach through
positive two-block data supplies the endpoint, including maximal spectral
curvature. No division by the vanished block is used. -/
theorem quartic_axis_bound
    {b s τ χ d f : ℝ} (hb : 0 < b) (hs : 1 ≤ s) (hs2 : s ≤ 2)
    (hbs : b * s ≤ 2) (hτ : τ = (3 * s - s ^ 3) / 2)
    (hχ : χ ^ 2 = 1 - τ ^ 2) (hd : 0 ≤ d) (hf : (5 / 3) * d ≤ f) :
    axisEnergy 0 b τ χ d f ≤ -(2 / 5 : ℝ) * d * (d / b) := by
  let F : ℝ → ℝ := fun t => axisEnergy t ((1 - t) * b) τ χ d f +
    (2 / 5 - 3 * t * ((1 - t) * b) / 10) * d * (d / ((1 - t) * b))
  have hden : (1 - (0 : ℝ)) * b ≠ 0 := by simpa using ne_of_gt hb
  have hcont : ContinuousAt F 0 := by
    dsimp [F, axisEnergy, scalarWeight, projectionCoefficient, defectCoefficient]
    fun_prop (disch := assumption)
  have hpoint : ∀ t ∈ Set.Ioo (0 : ℝ) 1, F t ≤ 0 := by
    intro t ht
    have htb : 0 < (1 - t) * b := mul_pos (by linarith [ht.2]) hb
    have hspec : t * 1 + ((1 - t) * b) * s ≤ 2 := by
      have h := mul_le_mul_of_nonneg_left hbs (show 0 ≤ 1 - t by linarith [ht.2])
      nlinarith [ht.1]
    have h := quartic_energy_bound_gradient (r := 1) (σ := 1) (ρ := 0) (a := 0)
      (e := 0) (f := f) ht.1 htb (by norm_num) (by norm_num)
      hs hs2 hspec (by norm_num) (by norm_num) hτ hχ (by norm_num) hd
      (by norm_num) hf
    norm_num only [mul_zero, mul_one] at h
    rw [quarticEnergy_axis] at h
    dsimp [F]
    norm_num only [zero_add, zero_div, mul_zero, sub_zero] at h
    linarith
  have hzero : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, by norm_num⟩
  have hlimit := ContinuousWithinAt.closure_le hzero hcont.continuousWithinAt
    continuousWithinAt_const hpoint
  dsimp [F] at hlimit
  norm_num only [sub_zero, one_mul, zero_mul, sub_zero] at hlimit
  linarith

/-- The quartic estimate on the closed spectral domain. The two zero-set
hypotheses encode exactly that a vanished curvature block has zero derivative
energy there; they remove every singular divided term by its zero numerator. -/
theorem quartic_energy_bound_closed
    {v b r s σ τ ρ χ a d e f : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hr : 1 ≤ r) (hr2 : r ≤ 2) (hs : 1 ≤ s) (hs2 : s ≤ 2)
    (hspectral : v * r + b * s ≤ 2)
    (hσ : σ = (3 * r - r ^ 3) / 2) (hρ : ρ ^ 2 = 1 - σ ^ 2)
    (hτ : τ = (3 * s - s ^ 3) / 2) (hχ : χ ^ 2 = 1 - τ ^ 2)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (he : (5 / 3) * a ≤ e) (hf : (5 / 3) * d ≤ f)
    (hve : v = 0 → e = 0) (hbf : b = 0 → f = 0) :
    quarticEnergy v b ((5 / 3) * a) ((5 / 3) * d)
      (projectionCoefficient v (b * s) σ ρ) (projectionCoefficient b (v * r) τ χ)
      (defectCoefficient v (b * s)) (defectCoefficient b (v * r)) e f ≤
      -(2 / 5 - 3 * v * b / 10) * (a + d) * (a / v + d / b) := by
  by_cases hvzero : v = 0
  · have hezero := hve hvzero
    have hazero : a = 0 := by nlinarith
    subst v
    subst e
    subst a
    by_cases hbzero : b = 0
    · have hfzero := hbf hbzero
      have hdzero : d = 0 := by nlinarith
      subst b
      subst f
      subst d
      simp [quarticEnergy, gradientSum]
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
      have haxis := quartic_axis_bound hbpos hs hs2 (by simpa using hspectral) hτ hχ hd hf
      simp only [mul_zero, zero_mul, zero_add, sub_zero, zero_div]
      rw [quarticEnergy_axis]
      exact haxis
  · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hvzero)
    by_cases hbzero : b = 0
    · have hfzero := hbf hbzero
      have hdzero : d = 0 := by nlinarith
      subst b
      subst f
      subst d
      have haxis := quartic_axis_bound hvpos hr hr2 (by simpa using hspectral) hσ hρ ha he
      simp only [mul_zero, zero_mul, add_zero, sub_zero, zero_div]
      rw [quarticEnergy_swap, quarticEnergy_axis]
      exact haxis
    · exact quartic_energy_bound_gradient hvpos (lt_of_le_of_ne hb (Ne.symm hbzero))
        hr hr2 hs hs2 hspectral hσ hρ hτ hχ ha hd he hf

end
end PositiveEinsteinFour.QuarticClosed

end OAI
