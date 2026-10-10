import OAI.NumberTheory.CubicMoment.Estimates.IdealMangoldtDyadic

namespace OAI

/-! Quantitative removal of the narrowing logarithmic cutoff. The error
is bounded by the actual ideal lattice in its two endpoint annuli. -/
noncomputable section
namespace CubicFirstMoment

lemma primeReciprocal_exp_bounds {J : ℝ} (hJ : 1 ≤ J) :
    Real.exp (-1/J) ≤ 1 ∧ 1 ≤ Real.exp (1/J) ∧ Real.exp (1/J) ≤ 3 ∧
    1-Real.exp (-1/J) ≤ 2/J ∧ Real.exp (1/J)-1 ≤ 2/J := by
  have hJ0 : 0 < J := zero_lt_one.trans_le hJ
  have ht : 0 ≤ 1/J := by positivity
  have ht1 : 1/J ≤ 1 := (div_le_one hJ0).mpr hJ
  have hu := Real.abs_exp_sub_one_le (x := 1/J) (by rwa [abs_of_nonneg ht])
  have hl := Real.abs_exp_sub_one_le (x := -1/J) (by
    rw [neg_div,abs_neg,abs_of_nonneg ht]; exact ht1)
  rw [abs_of_nonneg ht] at hu
  rw [neg_div,abs_neg,abs_of_nonneg ht] at hl
  have he := Real.one_le_exp ht
  have he' : Real.exp (-1/J) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    rw [neg_div]
    linarith
  refine ⟨he',he,?_,?_,?_⟩
  · linarith [(le_abs_self (Real.exp (1/J)-1)).trans hu]
  · have hh := (neg_le_abs (Real.exp (-(1/J))-1)).trans hl
    rw [←neg_div] at hh
    rw [show (2:ℝ)/J = 2*(1/J) by ring]
    linarith
  · rw [show (2:ℝ)/J = 2*(1/J) by ring]
    linarith [(le_abs_self (Real.exp (1/J)-1)).trans hu]

theorem idealMangoldt_dyadic_smoothing_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {J X : ℝ} (hJ : 1 ≤ J) (hX : Real.exp 1 ≤ X) :
    ‖idealMangoldtSmooth χ (primeDyadicWeight J hJ) X-idealMangoldtDyadic χ X‖ ≤
      32*(X/J+Real.sqrt X)*Real.log (6*X) := by
  have hX1 : 1 ≤ X := (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans hX
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  obtain ⟨heL,heU,he3,hdL,hdU⟩ := primeReciprocal_exp_bounds hJ
  have hrec : 1/J ≤ 1 := (div_le_one hJp).mpr hJ
  have hA1 : 1 ≤ Real.exp (-1/J)*X := by
    calc
      1 ≤ Real.exp (-1/J)*Real.exp 1 := by
        rw [←Real.exp_add]
        apply Real.one_le_exp
        rw [neg_div]
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hX (Real.exp_pos _).le
  have hAX : Real.exp (-1/J)*X ≤ X := mul_le_of_le_one_left hXp.le heL
  have hBX : 2*Real.exp (1/J)*X ≤ 6*X := by nlinarith
  have hdLX : X-Real.exp (-1/J)*X ≤ 2*(X/J) := by
    have hh := mul_le_mul_of_nonneg_right hdL hXp.le
    convert hh using 1 <;> ring
  have hdUX : 2*Real.exp (1/J)*X-2*X ≤ 4*(X/J) := by
    have hh := mul_le_mul_of_nonneg_right hdU (show 0 ≤ 2*X by positivity)
    convert hh using 1 <;> ring
  have hsA : Real.sqrt (Real.exp (-1/J)*X) ≤ Real.sqrt X := Real.sqrt_le_sqrt hAX
  have hsB : Real.sqrt (2*Real.exp (1/J)*X) ≤ 3*Real.sqrt X := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    nlinarith [Real.sq_sqrt hXp.le]
  have hs2 : Real.sqrt (2*X) ≤ 2*Real.sqrt X := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    nlinarith [Real.sq_sqrt hXp.le]
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hl6 : 0 ≤ Real.log (6*X) := Real.log_nonneg (by linarith)
  have hlogs : Real.log X ≤ Real.log (6*X) := Real.log_le_log hXp (by linarith)
  have hlogsB : Real.log (2*Real.exp (1/J)*X) ≤ Real.log (6*X) :=
    Real.log_le_log (by positivity) hBX
  have hlow : 4*(X-Real.exp (-1/J)*X+Real.sqrt X+Real.sqrt (Real.exp (-1/J)*X))*Real.log X ≤
      4*(2*(X/J)+2*Real.sqrt X)*Real.log (6*X) := by
    apply mul_le_mul _ hlogs hlX (by positivity)
    linarith
  have hupp : 4*(2*Real.exp (1/J)*X-2*X+Real.sqrt (2*Real.exp (1/J)*X)+Real.sqrt (2*X))*
      Real.log (2*Real.exp (1/J)*X) ≤
      4*(4*(X/J)+5*Real.sqrt X)*Real.log (6*X) := by
    apply mul_le_mul _ hlogsB (Real.log_nonneg (by nlinarith)) (by positivity)
    linarith
  calc
    _ ≤ _ := idealMangoldt_dyadic_smoothing_error χ hχ hJ hXp hA1
    _ ≤ 4*(2*(X/J)+2*Real.sqrt X)*Real.log (6*X)+
        4*(4*(X/J)+5*Real.sqrt X)*Real.log (6*X) := add_le_add hlow hupp
    _ ≤ _ := by nlinarith [mul_nonneg (div_nonneg hXp.le hJp.le) hl6,
      mul_nonneg (Real.sqrt_nonneg X) hl6]

end CubicFirstMoment

end

end OAI
