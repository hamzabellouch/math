import OAI.Geometry.NodalSets.Elliptic.CorrugationWellSlope

namespace OAI

namespace Yau.Geometry
open Real Set
open scoped ContDiff
noncomputable section

def flatRimWeight (t : ℝ) : ℝ := (t⁻¹)^2 * expNegInvGlue (8*t)

lemma flatRimWeight_continuous : Continuous flatRimWeight := by
  have h := (expNegInvGlue.continuous_polynomial_eval_inv_mul (Polynomial.X^2)).comp
    (continuous_const.mul continuous_id : Continuous (fun t : ℝ ↦ 8*t))
  have he : flatRimWeight = fun t ↦ 64 * ((Polynomial.X^2 : Polynomial ℝ).eval (8*t)⁻¹ * expNegInvGlue (8*t)) := by
    funext t
    simp [flatRimWeight,mul_inv_rev,mul_pow]
    ring
  rw [he]
  exact continuous_const.mul h

lemma flatRimWeight_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0:ℝ) 1, flatRimWeight t ≤ M := by
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image flatRimWeight_continuous.continuousOn
  exact ⟨max M 0,le_max_right _ _,fun t ht ↦ (hM ⟨t,ht,rfl⟩).trans (le_max_left _ _)⟩

lemma flatExponential_split {t : ℝ} (ht : 0 < t) :
    expNegInvGlue t = expNegInvGlue (8*t) * (expNegInvGlue t)^((7:ℝ)/8) := by
  have ht8 : 0 < 8*t := by positivity
  simp only [expNegInvGlue,ite_eq_right (not_le.mpr ht),ite_eq_right (not_le.mpr ht8)]
  rw [← Real.exp_mul,← Real.exp_add]
  congr 1
  simp [mul_inv_rev]
  ring

theorem corrugationSlope_fractional_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (a R r : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ R → R ≤ 1 → 0 ≤ r →
      max (-(deriv (corrugationSlope a R) r)) 0 ≤ C * (corrugationSlope a R r)^((7:ℝ)/8) := by
  obtain ⟨M,hM,hbound⟩ := flatRimWeight_bounded
  refine ⟨2*M+1,by linarith,?_⟩
  intro a R r ha ha1 hR hR1 hr
  by_cases ht : 0 < R^2-r^2
  · have hr1 : r ≤ 1 := by nlinarith
    have ht1 : R^2-r^2 ≤ 1 := by nlinarith [sq_nonneg r]
    have hw := hbound (R^2-r^2) ⟨ht.le,ht1⟩
    have har : 0 ≤ a*r := mul_nonneg ha hr
    have har1 : a*r ≤ 1 := by nlinarith
    have hpow : a*r ≤ (a*r)^((7:ℝ)/8) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge' har har1
        (show 0 ≤ (7:ℝ)/8 by norm_num) (show (7:ℝ)/8 ≤ 1 by norm_num)
    have har2 : a*r^2 ≤ (a*r)^((7:ℝ)/8) :=
      (show a*r^2 ≤ a*r by nlinarith).trans hpow
    have hg := expNegInvGlue.nonneg (R^2-r^2)
    have hgp := Real.rpow_nonneg hg ((7:ℝ)/8)
    have hw0 : 0 ≤ flatRimWeight (R^2-r^2) := by
      unfold flatRimWeight
      exact mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg _)
    calc
      max (-(deriv (corrugationSlope a R) r)) 0 ≤
          2*a*r^2*((R^2-r^2)⁻¹)^2*expNegInvGlue (R^2-r^2) :=
        corrugationSlope_negative_deriv_le ha
      _ = 2*(a*r^2)*flatRimWeight (R^2-r^2)*(expNegInvGlue (R^2-r^2))^((7:ℝ)/8) := by
        conv_lhs => rw [flatExponential_split ht]
        unfold flatRimWeight
        ring
      _ ≤ 2*(a*r)^((7:ℝ)/8)*M*(expNegInvGlue (R^2-r^2))^((7:ℝ)/8) := by
        gcongr
      _ ≤ (2*M+1)*(corrugationSlope a R r)^((7:ℝ)/8) := by
        rw [corrugationSlope,Real.mul_rpow har hg]
        nlinarith [mul_nonneg (Real.rpow_nonneg har ((7:ℝ)/8)) hgp]
  · have hz : expNegInvGlue (R^2-r^2) = 0 := expNegInvGlue.zero_of_nonpos (le_of_not_gt ht)
    simp [corrugationSlope_deriv,corrugationSlope,hz]

end
end Yau.Geometry

end OAI
