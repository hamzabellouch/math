import Mathlib

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem exp_quadratic_remainder (x : ℝ) :
    Real.exp x ≤ 1+x+x^2*Real.exp |x| := by
  have H := Complex.norm_exp_sub_sum_le_norm_mul_exp (x:ℂ) 2
  norm_num [Finset.sum_range_succ,← Complex.ofReal_exp,← Complex.ofReal_add,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs] at H
  have he : (↑(Real.exp x)-(1+(x:ℂ)))=((Real.exp x-(1+x):ℝ):ℂ) := by push_cast; ring
  rw [he,Complex.norm_real,Real.norm_eq_abs] at H
  have HL := le_abs_self (Real.exp x-(1+x))
  linarith

theorem fourth_pow_le_exp_square {c : ℝ} (hc : 0<c) (y : ℝ) :
    y^4 ≤ 2/c^2*Real.exp (c*y^2) := by
  have H := Real.pow_div_factorial_le_exp (c*y^2) (mul_nonneg hc.le (sq_nonneg y)) 2
  norm_num at H
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  calc
    y^4*c^2 ≤ 2*Real.exp (c*y^2) := by nlinarith
    _ = (2*Real.exp (c*y^2)) := rfl

theorem log_integral_exp_quadratic_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y Δ : Ω → ℝ)
    (hY : AEStronglyMeasurable Y μ) (hΔ : Integrable Δ μ)
    {c δ M : ℝ} (hc : 0<c) (hδ : 4*δ^2 ≤ c)
    (hE : Integrable (fun z => Real.exp (c*(Y z)^2)) μ)
    (hM : (∫ z, Real.exp (c*(Y z)^2) ∂μ) ≤ M)
    (hb : ∀ᵐ z ∂μ, |Δ z| ≤ 2*δ^2*(Y z)^2) :
    Real.log (∫ z, Real.exp (Δ z) ∂μ) ≤ (∫ z, Δ z ∂μ)+
      (32/c^2)*δ^4*M := by
  have hE : Integrable (fun z => Real.exp (c*(Y z)^2)) μ :=
    ⟨Real.continuous_exp.comp_aestronglyMeasurable ((hY.pow 2).const_mul c),
      hE.hasFiniteIntegral⟩
  have hη : ∀ z, 2*δ^2*(Y z)^2 ≤ c/2*(Y z)^2 := by
    intro z
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hdom : ∀ᵐ z ∂μ, Real.exp (Δ z) ≤ Real.exp (c*(Y z)^2) := by
    filter_upwards [hb] with z hz
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (hz.trans (by
      have H := hη z
      nlinarith [mul_nonneg hc.le (sq_nonneg (Y z))]))
  have hi : Integrable (fun z => Real.exp (Δ z)) μ :=
    hE.mono' (Real.continuous_exp.comp_aestronglyMeasurable hΔ.aestronglyMeasurable) (by
      filter_upwards [hdom] with z hz
      simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hz)
  have hpos : 0 < (∫ z, Real.exp (Δ z) ∂μ) := integral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun z => (Real.exp_pos (Δ z)).le)) hi |>.mpr (by simp [Function.support,Real.exp_ne_zero])
  have hr : ∀ᵐ z ∂μ, Real.exp (Δ z) ≤ 1+Δ z+
      (32/c^2)*δ^4*Real.exp (c*(Y z)^2) := by
    filter_upwards [hb] with z hz
    apply (exp_quadratic_remainder (Δ z)).trans
    apply add_le_add_right
    have hsq : (Δ z)^2 ≤ 4*δ^4*(Y z)^4 := by
      have H := pow_le_pow_left₀ (abs_nonneg (Δ z)) hz 2
      rw [sq_abs] at H
      nlinarith [H]
    have hp := fourth_pow_le_exp_square (half_pos hc) (Y z)
    have hexp : Real.exp |Δ z| ≤ Real.exp (c/2*(Y z)^2) :=
      Real.exp_le_exp.mpr (hz.trans (hη z))
    calc
      _ ≤ (4*δ^4*(Y z)^4)*Real.exp (c/2*(Y z)^2) :=
        mul_le_mul hsq hexp (Real.exp_nonneg _) (by positivity)
      _ ≤ (4*δ^4*(2/(c/2)^2*Real.exp (c/2*(Y z)^2)))*Real.exp (c/2*(Y z)^2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (Real.exp_nonneg _)
      _ = (4*δ^4*(2/(c/2)^2))*(Real.exp (c/2*(Y z)^2)*Real.exp (c/2*(Y z)^2)) := by ring
      _ = _ := by
        rw [← Real.exp_add,show c/2*(Y z)^2+c/2*(Y z)^2=c*(Y z)^2 by ring]
        congr 1
        field_simp
        ring
  have H := integral_mono_ae hi ((integrable_const (1:ℝ)).add hΔ |>.add (hE.const_mul ((32/c^2)*δ^4))) hr
  simp only [Pi.add_apply] at H
  have Hsum := integral_add ((integrable_const (1:ℝ)).add hΔ) (hE.const_mul ((32/c^2)*δ^4))
  have Hsum2 := integral_add (integrable_const (1:ℝ)) hΔ
  simp only [Pi.add_apply] at Hsum Hsum2
  rw [Hsum,Hsum2,integral_const_mul] at H
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at H
  have HM := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ (32/c^2)*δ^4)
  have HL := Real.log_le_sub_one_of_pos hpos
  linarith

end SK.Analytic

end
end

end OAI
