import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingInverse

namespace OAI

/-! Weak Vinogradov--Korobov growth for the Hurwitz zeta function with
its first term removed, and the finite-character reduction. -/

namespace TwoPointCorrelations

open Complex Finset HurwitzZeta
open scoped Classical

noncomputable def mrtVKLog (t : ℝ) : ℝ := Real.log (|t| + 3)

noncomputable def mrtVKRadius (t : ℝ) : ℝ := (mrtVKLog t) ^ (-(2 / 3 : ℝ))

noncomputable def mrtHurwitzFirstTerm (a : ℝ) (s : ℂ) : ℂ :=
  if a = 0 then 0 else (a : ℂ) ^ (-s)

/-- A polynomial logarithmic bound on the shrinking VK disk. Removing the
first Hurwitz term makes the bound uniform down to `a = 0`. -/
def MRTWeakHurwitzGrowthInput : Prop :=
  ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ t : ℝ, T ≤ |t| →
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ s : ℂ,
      1 - mrtVKRadius t ≤ s.re → s.re ≤ 1 + 5 * mrtVKRadius t →
      |s.im - t| ≤ 3 * mrtVKRadius t →
        ‖hurwitzZeta (a : UnitAddCircle) s - mrtHurwitzFirstTerm a s‖ ≤ (mrtVKLog t) ^ C

lemma mrt_hurwitz_first_term_bound {q : ℕ} [NeZero q] (j : ZMod q)
    {s : ℂ} (hs : s.re ≤ 2) :
    ‖mrtHurwitzFirstTerm ((j.val : ℝ) / q) s‖ ≤ (q : ℝ) ^ 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have ha : (j.val : ℝ) / q ≤ 1 := by
    exact (div_le_one hq).mpr (by exact_mod_cast (ZMod.val_lt j).le)
  by_cases hj : j.val = 0
  · simp [mrtHurwitzFirstTerm, hj]
  have hjp : (0 : ℝ) < j.val := by exact_mod_cast Nat.pos_of_ne_zero hj
  have ha0 : 0 < (j.val : ℝ) / q := div_pos hjp hq
  have hlo : 1 / (q : ℝ) ≤ (j.val : ℝ) / q :=
    div_le_div_of_nonneg_right (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj) hq.le
  rw [mrtHurwitzFirstTerm, ite_eq_right ha0.ne', Complex.norm_cpow_eq_rpow_re_of_pos ha0,
    Complex.neg_re]
  calc
    _ ≤ ((j.val : ℝ) / q) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ha0 ha (by linarith)
    _ ≤ (1 / (q : ℝ)) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by norm_num)
    _ = (q : ℝ) ^ 2 := by norm_num [Real.rpow_neg (by positivity : 0 ≤ 1 / (q : ℝ)),
      Real.rpow_two, one_div]

/-- Exact finite Hurwitz decomposition retains a polynomial modulus cost. -/
theorem mrt_character_of_hurwitz_growth {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} {A : ℝ}
    (hσ : 0 ≤ s.re) (hσ2 : s.re ≤ 2)
    (hh : ∀ a ∈ Set.Icc (0 : ℝ) 1,
      ‖hurwitzZeta (a : UnitAddCircle) s - mrtHurwitzFirstTerm a s‖ ≤ A) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (q : ℝ) * ((q : ℝ) ^ 2 + A) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hb (j : ZMod q) :
      ‖hurwitzZeta (ZMod.toAddCircle j) s‖ ≤ (q : ℝ) ^ 2 + A := by
    have ha : (j.val : ℝ) / q ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one (by positivity : (0 : ℝ) < q)).mpr
        (by exact_mod_cast (ZMod.val_lt j).le)⟩
    have he := norm_add_le
      (hurwitzZeta (((j.val : ℝ) / (q : ℝ)) : UnitAddCircle) s -
        mrtHurwitzFirstTerm ((j.val : ℝ) / q) s)
      (mrtHurwitzFirstTerm ((j.val : ℝ) / q) s)
    rw [sub_add_cancel] at he
    rw [ZMod.toAddCircle_apply]
    exact he.trans (by linarith [hh _ ha, mrt_hurwitz_first_term_bound j hσ2])
  have hpow : ‖(q : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos
      (by positivity : (0 : ℝ) < q), Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith)
  unfold DirichletCharacter.LFunction ZMod.LFunction
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖∑ j : ZMod q, χ j * hurwitzZeta (ZMod.toAddCircle j) s‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ ∑ j : ZMod q, ‖χ j * hurwitzZeta (ZMod.toAddCircle j) s‖ := by
      simpa only [one_mul] using norm_sum_le (Finset.univ) _
    _ ≤ ∑ _j : ZMod q, ((q : ℝ) ^ 2 + A) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      calc
        _ ≤ 1 * ((q : ℝ) ^ 2 + A) := mul_le_mul (χ.norm_le_one _) (hb j)
          (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    _ = (q : ℝ) * ((q : ℝ) ^ 2 + A) := by simp [mul_add]

lemma mrt_moving_point_region {r t : ℝ} (hr : 0 ≤ r)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    1 - r ≤ (mrtMovingPoint r t z).re ∧
      (mrtMovingPoint r t z).re ≤ 1 + 5 * r ∧
      |(mrtMovingPoint r t z).im - t| ≤ 3 * r := by
  have hre := abs_le.mp ((Complex.abs_re_le_norm z).trans hz)
  have him := (Complex.abs_im_le_norm z).trans hz
  simp only [mrtMovingPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero,
    Complex.add_im, Complex.mul_im, zero_add]
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  rw [add_sub_cancel_left, add_zero, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3 * r)]
  nlinarith

/-- Applying the weak Hurwitz input to the actual moving character disk. -/
theorem MRTWeakHurwitzGrowthInput.character_disk (h : MRTWeakHurwitzGrowthInput) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ t : ℝ, T ≤ |t| →
      mrtVKRadius t ≤ 1 / 5 → ∀ (q : ℕ) [NeZero q],
      ∀ (χ : DirichletCharacter ℂ q), ∀ z : ℂ, ‖z‖ ≤ 1 →
        ‖DirichletCharacter.LFunction χ (mrtMovingPoint (mrtVKRadius t) t z)‖ ≤
          (q : ℝ) * ((q : ℝ) ^ 2 + (mrtVKLog t) ^ C) := by
  obtain ⟨C, T, hC, hT, hg⟩ := h
  refine ⟨C, T, hC, hT, ?_⟩
  intro t ht hr q _ χ z hz
  have hrr : 0 ≤ mrtVKRadius t := Real.rpow_nonneg
    (le_of_lt (Real.log_pos (by linarith [abs_nonneg t] : 1 < |t| + 3))) _
  have hreg := mrt_moving_point_region (t := t) hrr hz
  apply mrt_character_of_hurwitz_growth χ (by linarith [hreg.1])
    (by linarith [hreg.2.1])
  intro a ha
  exact hg t ht a ha _ hreg.1 hreg.2.1 hreg.2.2

end TwoPointCorrelations

end OAI
