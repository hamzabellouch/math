import OAI.NumberTheory.CubicMoment.Estimates.PrimeContourOptimization

namespace OAI

/-! Comparison of the prime contour majorant over the upper half of a
contracting dyadic partition. -/
noncomputable section
namespace CubicFirstMoment

def primeCancellationWeight (c Q X : ℝ) : ℝ :=
  X*(Real.log (X*Q))^2*Real.exp (-c*Real.log X/primeContourDenominator Q X)

lemma primeDyadic_log_bounds {X t : ℝ} (hXp : 0 < X) (hX : 2 ≤ Real.log X)
    (ht : Real.sqrt X ≤ t) (htX : t ≤ X) :
    0 < t ∧ 1 ≤ Real.log t ∧ Real.log X/2 ≤ Real.log t ∧ Real.log t ≤ Real.log X := by
  have htp : 0 < t := (Real.sqrt_pos.mpr hXp).trans_le ht
  have hlo := Real.log_le_log (Real.sqrt_pos.mpr hXp) ht
  rw [Real.log_sqrt hXp.le] at hlo
  exact ⟨htp,by linarith,hlo,Real.log_le_log htp htX⟩

lemma primeDyadic_ratio_compare {Q X t : ℝ} (hQ : 1 ≤ Q) (hXp : 0 < X)
    (hX : 2 ≤ Real.log X) (ht : Real.sqrt X ≤ t) (htX : t ≤ X) :
    (Real.log X/primeContourDenominator Q X)/2 ≤
      Real.log t/primeContourDenominator Q t := by
  obtain ⟨htp,hlt,hlo,hhi⟩ := primeDyadic_log_bounds hXp hX ht htX
  have hdX := primeContourDenominator_ge_one hQ (by linarith : 1 ≤ Real.log X)
  have hdt := primeContourDenominator_ge_one hQ hlt
  have hden : primeContourDenominator Q t ≤ primeContourDenominator Q X := by
    unfold primeContourDenominator
    linarith [Real.sqrt_le_sqrt hhi]
  calc
    _ = (Real.log X/2)/primeContourDenominator Q X := by ring
    _ ≤ Real.log t/primeContourDenominator Q X :=
      div_le_div_of_nonneg_right hlo (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_left (by linarith) (by linarith) hden

lemma primeDyadic_majorant_compare {c Q X t : ℝ} (hc : 0 ≤ c) (hQ : 1 ≤ Q)
    (hXp : 0 < X) (hX : 2 ≤ Real.log X) (ht : Real.sqrt X ≤ t) (htX : t ≤ X) :
    primeCancellationWeight c Q t ≤
      t*(Real.log (X*Q))^2*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X) := by
  obtain ⟨htp,hlt,_,_⟩ := primeDyadic_log_bounds hXp hX ht htX
  have hl : Real.log (t*Q) ≤ Real.log (X*Q) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right htX (by linarith))
  have hl0 : 0 ≤ Real.log (t*Q) := by
    have hh := (primeLogSize_bounds hQ htp hlt).1
    linarith
  have hsq := pow_le_pow_left₀ hl0 hl 2
  have he : Real.exp (-c*Real.log t/primeContourDenominator Q t) ≤
      Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (primeDyadic_ratio_compare hQ hXp hX ht htX) hc
    simp only [div_eq_mul_inv] at *
    nlinarith only [hh]
  unfold primeCancellationWeight
  exact mul_le_mul (mul_le_mul_of_nonneg_left hsq htp.le) he
    (Real.exp_pos _).le (by positivity)

lemma primeDyadic_sqrt_absorption {c Q X t : ℝ} (_hc : 0 ≤ c) (hc1 : c ≤ 1/2)
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X)
    (ht : Real.sqrt X ≤ t) (htX : t ≤ X) :
    Real.sqrt t ≤ t*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X) := by
  obtain ⟨htp,hlt,hlo,_⟩ := primeDyadic_log_bounds hXp hX ht htX
  have hy := primeContour_ratio_bounds hQ (by linarith : 1 ≤ Real.log X)
  have hh := mul_le_mul_of_nonneg_right hc1 hy.1
  have hs : Real.sqrt t = Real.exp (Real.log t/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos htp]
    congr 1
    ring
  calc
    _ = Real.exp (Real.log t/2) := hs
    _ ≤ Real.exp (Real.log t+-(c/2)*Real.log X/primeContourDenominator Q X) := by
      apply Real.exp_le_exp.mpr
      simp only [div_eq_mul_inv] at *
      nlinarith [hy.2.2]
    _ = _ := by rw [Real.exp_add,Real.exp_log htp]

lemma primeDyadic_boundary_compare {c Q X t : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1/2)
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X)
    (ht : Real.sqrt X ≤ t) (htX : t ≤ X) :
    8*Real.sqrt t*Real.log t ≤
      8*(t*(Real.log (X*Q))^2*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X)) := by
  obtain ⟨htp,hlt,_,hhi⟩ := primeDyadic_log_bounds hXp hX ht htX
  have hP := (primeLogSize_bounds hQ hXp (by linarith)).1
  have hLP := (primeLogSize_bounds hQ hXp (by linarith)).2.1
  have hlog : Real.log t ≤ (Real.log (X*Q))^2 := by nlinarith
  have hh := mul_le_mul (primeDyadic_sqrt_absorption hc hc1 hQ hXp hX ht htX)
    hlog (by linarith : 0 ≤ Real.log t) (by positivity)
  nlinarith only [hh]

lemma primeDyadic_small_compare {c Q X r : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1/2)
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X)
    (hr : 1 ≤ r) (hrX : r ≤ X) (hrs : r ≤ 2*Real.sqrt X) :
    8*r*Real.log r ≤ 16*primeCancellationWeight (c/2) Q X := by
  have hroot : Real.sqrt X ≤ X := by
    have hx1 : 1 ≤ X := by
      have hh := Real.exp_le_exp.mpr (show (0:ℝ) ≤ Real.log X by linarith)
      simpa [Real.exp_log hXp] using hh
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hXp.le,by nlinarith⟩
  have hsq := primeDyadic_sqrt_absorption hc hc1 hQ hXp hX hroot le_rfl
  have hP := (primeLogSize_bounds hQ hXp (by linarith)).1
  have hLP := (primeLogSize_bounds hQ hXp (by linarith)).2.1
  have hlog : Real.log r ≤ (Real.log (X*Q))^2 := by
    have hh := Real.log_le_log (by linarith : 0 < r) hrX
    nlinarith
  have hh := mul_le_mul hrs hlog (Real.log_nonneg hr) (by positivity : 0 ≤ 2*Real.sqrt X)
  have hhh := mul_le_mul_of_nonneg_right hsq (sq_nonneg (Real.log (X*Q)))
  unfold primeCancellationWeight
  nlinarith only [hh,hhh]

end CubicFirstMoment

end

end OAI
