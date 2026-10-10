import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem336
namespace Innovation

theorem norm_exp_I_taylor_two (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
      (x : ℂ) ^ 2 / 2‖ ≤ 4 * |x| ^ 3 := by
  have hnorm : ‖(x : ℂ) * Complex.I‖ = |x| := by simp
  by_cases hx : |x| ≤ 1
  · have hb := Complex.exp_bound (x := (x : ℂ) * Complex.I)
      (by simpa only [hnorm] using hx) (n := 3) (by decide)
    have hpoly : (∑ m ∈ Finset.range 3,
        ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) =
        1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2 := by
      norm_num [Finset.sum_range_succ, mul_pow, Complex.I_sq]
      ring
    rw [hpoly, hnorm] at hb
    norm_num at hb
    have heq : Complex.exp ((x : ℂ) * Complex.I) -
        (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2) =
        Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
          (x : ℂ) ^ 2 / 2 := by ring
    rw [heq] at hb
    nlinarith [pow_nonneg (abs_nonneg x) 3]
  · have hx1 : 1 ≤ |x| := (lt_of_not_ge hx).le
    have hsq : |x| ≤ |x| ^ 2 := by nlinarith [mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hx1)]
    have hcube : |x| ^ 2 ≤ |x| ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg |x|) (sub_nonneg.mpr hx1)]
    calc
      ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
          (x : ℂ) ^ 2 / 2‖
          ≤ ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I‖ +
              ‖(x : ℂ) ^ 2 / 2‖ := norm_add_le _ _
      _ ≤ (‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ +
              ‖(x : ℂ) * Complex.I‖) + ‖(x : ℂ) ^ 2 / 2‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ((‖Complex.exp ((x : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖) +
              ‖(x : ℂ) * Complex.I‖) + ‖(x : ℂ) ^ 2 / 2‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = 2 + |x| + |x| ^ 2 / 2 := by simp [norm_pow]; ring
      _ ≤ 4 * |x| ^ 3 := by nlinarith

theorem norm_integral_weighted_taylor {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (D : Ω → ℝ) (K : Ω → ℂ)
    (hK : ∀ᵐ ω ∂P, ‖K ω‖ ≤ 1)
    (hthird : Integrable (fun ω => |D ω| ^ 3) P) :
    ‖∫ ω, K ω * (Complex.exp ((D ω : ℂ) * Complex.I) - 1 -
        (D ω : ℂ) * Complex.I + (D ω : ℂ) ^ 2 / 2) ∂P‖ ≤
      4 * ∫ ω, |D ω| ^ 3 ∂P := by
  calc
    _ ≤ ∫ ω, 4 * |D ω| ^ 3 ∂P := by
      apply norm_integral_le_of_norm_le (hthird.const_mul 4)
      filter_upwards [hK] with ω hω
      rw [norm_mul]
      calc
        _ ≤ 1 * ‖Complex.exp ((D ω : ℂ) * Complex.I) - 1 -
            (D ω : ℂ) * Complex.I + (D ω : ℂ) ^ 2 / 2‖ :=
          mul_le_mul_of_nonneg_right hω (norm_nonneg _)
        _ ≤ 4 * |D ω| ^ 3 := by simpa using norm_exp_I_taylor_two (D ω)
    _ = _ := integral_const_mul 4 _

theorem characteristic_second_order {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (D : Ω → ℝ) (K : Ω → ℂ)
    (hK : ∀ᵐ ω ∂P, ‖K ω‖ ≤ 1)
    (hthird : Integrable (fun ω => |D ω| ^ 3) P)
    (hconst : Integrable K P)
    (hlinear : Integrable (fun ω => K ω * (D ω : ℂ)) P)
    (hquad : Integrable (fun ω => K ω * (D ω : ℂ) ^ 2) P)
    (hchar : Integrable (fun ω => K ω * Complex.exp ((D ω : ℂ) * Complex.I)) P)
    (hmean : (∫ ω, K ω * (D ω : ℂ) ∂P) = 0) :
    ‖(∫ ω, K ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂P) -
        (∫ ω, K ω ∂P) + (∫ ω, K ω * (D ω : ℂ) ^ 2 ∂P) / 2‖ ≤
      4 * ∫ ω, |D ω| ^ 3 ∂P := by
  have hbound := norm_integral_weighted_taylor P D K hK hthird
  have hfun : (fun ω => K ω * (Complex.exp ((D ω : ℂ) * Complex.I) - 1 -
        (D ω : ℂ) * Complex.I + (D ω : ℂ) ^ 2 / 2)) =
      (fun ω => (K ω * Complex.exp ((D ω : ℂ) * Complex.I) - K ω) -
        (K ω * (D ω : ℂ)) * Complex.I + (K ω * (D ω : ℂ) ^ 2) / 2) := by
    funext ω
    ring
  rw [hfun] at hbound
  have hadd := integral_add ((hchar.sub hconst).sub (hlinear.mul_const Complex.I))
      (hquad.div_const 2)
  have hsub := integral_sub (hchar.sub hconst) (hlinear.mul_const Complex.I)
  have hsub' := integral_sub hchar hconst
  simp only [Pi.sub_apply] at hadd hsub hsub'
  rw [hadd, hsub, hsub', integral_mul_const, integral_div, hmean] at hbound
  simpa using hbound

theorem gaussian_approximation_of_moments {A B M : ℂ} {r d q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hB : ‖B‖ ≤ 1)
    (hTaylor : ‖A - B + M / 2‖ ≤ r)
    (hMoment : ‖M - (2 * q : ℝ) * B‖ ≤ d) :
    ‖A - (Real.exp (-q) : ℂ) * B‖ ≤ r + d / 2 + q ^ 2 := by
  have hexp : |Real.exp (-q) - 1 + q| ≤ q ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le (x := -q)
      (by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)
    simpa [Real.norm_eq_abs, sub_neg_eq_add] using h
  have hdecomp : A - (Real.exp (-q) : ℂ) * B =
      (A - B + M / 2) - (M - (2 * q : ℝ) * B) / 2 -
        ((Real.exp (-q) - 1 + q : ℝ) : ℂ) * B := by
    push_cast
    ring
  rw [hdecomp]
  calc
    _ ≤ ‖A - B + M / 2‖ + ‖(M - (2 * q : ℝ) * B) / 2‖ +
        ‖((Real.exp (-q) - 1 + q : ℝ) : ℂ) * B‖ := by
      apply (norm_sub_le _ _).trans
      gcongr
      exact norm_sub_le _ _
    _ ≤ r + d / 2 + q ^ 2 := by
      have hdiv : ‖(M - (2 * q : ℝ) * B) / 2‖ ≤ d / 2 := by
        simpa [norm_div] using div_le_div_of_nonneg_right hMoment (by norm_num : (0 : ℝ) ≤ 2)
      have hmul : ‖((Real.exp (-q) - 1 + q : ℝ) : ℂ) * B‖ ≤ q ^ 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc
          _ ≤ q ^ 2 * 1 := mul_le_mul hexp hB (norm_nonneg _) (sq_nonneg _)
          _ = q ^ 2 := mul_one _
      exact add_le_add (add_le_add hTaylor hdiv) hmul

theorem weighted_characteristic_gaussian_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → ℝ) (K : Ω → ℂ)
    (hKmeas : AEStronglyMeasurable K P) (hK : ∀ᵐ ω ∂P, ‖K ω‖ ≤ 1)
    (hfirst : Integrable D P) (hsecond : Integrable (fun ω => D ω ^ 2) P)
    (hthird : Integrable (fun ω => |D ω| ^ 3) P)
    (hmean : (∫ ω, K ω * (D ω : ℂ) ∂P) = 0)
    {q δ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hsecond_est : ‖(∫ ω, K ω * (D ω : ℂ) ^ 2 ∂P) -
      (2 * q : ℝ) * (∫ ω, K ω ∂P)‖ ≤ δ) :
    ‖(∫ ω, K ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂P) -
      (Real.exp (-q) : ℂ) * (∫ ω, K ω ∂P)‖ ≤
      4 * (∫ ω, |D ω| ^ 3 ∂P) + δ / 2 + q ^ 2 := by
  have hconst : Integrable K P := Integrable.of_bound hKmeas 1 hK
  have hlinear : Integrable (fun ω => K ω * (D ω : ℂ)) P :=
    hfirst.ofReal.bdd_mul hKmeas hK
  have hsq : Integrable (fun ω => (D ω : ℂ) ^ 2) P := by
    have h : Integrable (fun ω => ((D ω ^ 2 : ℝ) : ℂ)) P := hsecond.ofReal
    simpa only [Complex.ofReal_pow] using h
  have hquad : Integrable (fun ω => K ω * (D ω : ℂ) ^ 2) P :=
    hsq.bdd_mul hKmeas hK
  have hphase : AEStronglyMeasurable
      (fun ω => Complex.exp ((D ω : ℂ) * Complex.I)) P :=
    Complex.continuous_exp.comp_aestronglyMeasurable
      ((hfirst.ofReal : Integrable (fun ω => (D ω : ℂ)) P).aestronglyMeasurable.mul_const _)
  have hphase_int : Integrable (fun ω => Complex.exp ((D ω : ℂ) * Complex.I)) P :=
    Integrable.of_bound hphase 1 (Filter.Eventually.of_forall (fun ω => by simp))
  have hchar : Integrable (fun ω => K ω * Complex.exp ((D ω : ℂ) * Complex.I)) P :=
    hphase_int.bdd_mul hKmeas hK
  have hB : ‖∫ ω, K ω ∂P‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le (integrable_const (1 : ℝ)) hK
  exact gaussian_approximation_of_moments hq0 hq1 hB
    (characteristic_second_order P D K hK hthird hconst hlinear hquad hchar hmean)
    hsecond_est

end Innovation
end Problem336

end

end OAI
