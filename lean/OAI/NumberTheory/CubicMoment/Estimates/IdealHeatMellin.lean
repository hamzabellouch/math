import OAI.NumberTheory.CubicMoment.Estimates.IdealHeatTheta
import OAI.NumberTheory.CubicMoment.Estimates.IdealThetaMellin

namespace OAI

/-! The Gamma(s+kappa) factor obtained from the actual normalized angular
heat kernel; all positive ideals remain in the Dirichlet series. -/
noncomputable section
namespace CubicFirstMoment

lemma idealHeatTheta_one_term (κ : ℝ) (χ : EisensteinIdealExponent → ℂ)
    (ν : EisensteinIdealExponent) {t : ℝ} (ht : 0 < t) :
    χ ν*((idealExponentNorm ν*t/1)^κ*Real.exp (-idealExponentNorm ν*t/1):ℝ) =
      (t:ℂ)^(κ:ℂ) * (χ ν*(idealExponentNorm ν:ℂ)^(κ:ℂ)*
        (Real.exp (-idealExponentNorm ν*t):ℝ)) := by
  have hn := idealExponentNorm_pos ν
  rw [div_one,div_one,Real.mul_rpow hn.le ht.le,Complex.ofReal_mul,
    Complex.ofReal_mul,Complex.ofReal_cpow hn.le,Complex.ofReal_cpow ht.le]
  ring

lemma idealHeatTheta_one_factor (κ : ℝ) (χ : EisensteinIdealExponent → ℂ)
    {t : ℝ} (ht : 0 < t) :
    idealHeatTheta 1 κ χ t = (t:ℂ)^(κ:ℂ)*
      idealTheta 1 (fun ν => χ ν*(idealExponentNorm ν:ℂ)^(κ:ℂ)) t := by
  unfold idealHeatTheta idealTheta
  simp_rw [idealHeatTheta_one_term κ χ _ ht,div_one]
  exact tsum_mul_left

lemma idealHeatTheta_one_mellin {κ : ℝ} (hκ : 0 ≤ κ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (idealHeatTheta 1 κ χ) s =
      Complex.Gamma (s+(κ:ℂ))*normDirichletSeries χ idealExponentNorm s := by
  have hsum : Summable (fun ν => ‖χ ν*(idealExponentNorm ν:ℂ)^(κ:ℂ)‖ /
      idealExponentNorm ν^(s+(κ:ℂ)).re) := by
    convert summable_ideal_character_weight hs χ hχ using 1
    ext ν
    have hn := idealExponentNorm_pos ν
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hn,Complex.ofReal_re,
      Complex.add_re,Complex.ofReal_re,Real.rpow_add hn,Real.rpow_neg hn.le]
    field_simp
  have hseries (t : ℝ) (ht : 0 < t) :
      HasSum (fun ν => (χ ν*(idealExponentNorm ν:ℂ)^(κ:ℂ))*
        (Real.exp (-idealExponentNorm ν*t):ℝ))
        (idealTheta 1 (fun ν => χ ν*(idealExponentNorm ν:ℂ)^(κ:ℂ)) t) := by
    have hh := idealHeatTheta_summable zero_lt_one hκ ht χ hχ
    simp_rw [idealHeatTheta_one_term κ χ _ ht] at hh
    have hc : (t:ℂ)^(κ:ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne'))
    have hraw := (summable_mul_left_iff hc).mp hh
    simpa only [idealTheta,div_one] using hraw.hasSum
  have hm := hasSum_mellin (fun ν => Or.inr (idealExponentNorm_pos ν))
    (show 0 < (s+(κ:ℂ)).re by simp only [Complex.add_re,Complex.ofReal_re]; linarith)
    hseries hsum
  have he : mellin (idealHeatTheta 1 κ χ) s =
      mellin (idealTheta 1 (fun ν => χ ν*(idealExponentNorm ν:ℂ)^(κ:ℂ))) (s+(κ:ℂ)) := by
    rw [←mellin_cpow_smul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [idealHeatTheta_one_factor κ χ ht,smul_eq_mul]
  rw [he,←hm.tsum_eq]
  have ht (ν : EisensteinIdealExponent) :
      Complex.Gamma (s+(κ:ℂ))*(χ ν*(idealExponentNorm ν:ℂ)^(κ:ℂ)) /
        (idealExponentNorm ν:ℂ)^(s+(κ:ℂ)) =
      Complex.Gamma (s+(κ:ℂ))*(χ ν*(idealExponentNorm ν:ℂ)^(-s)) := by
    have hn := Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν).ne'
    rw [Complex.cpow_add _ _ hn,Complex.cpow_neg]
    have hnk : (idealExponentNorm ν:ℂ)^(κ:ℂ) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hn)
    field_simp
  simp_rw [ht]
  exact tsum_mul_left

lemma idealHeatTheta_scale (A κ : ℝ) (χ : EisensteinIdealExponent → ℂ) :
    idealHeatTheta A κ χ = fun t => idealHeatTheta 1 κ χ (t*(1/A)) := by
  funext t
  unfold idealHeatTheta
  apply tsum_congr
  intro ν
  have he : idealExponentNorm ν*t/A = idealExponentNorm ν*(t*(1/A))/1 := by ring
  have he' : -idealExponentNorm ν*t/A = -idealExponentNorm ν*(t*(1/A))/1 := by ring
  rw [he,he']

lemma idealHeatTheta_mellin {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (idealHeatTheta A κ χ) s =
      (A:ℂ)^s*Complex.Gamma (s+(κ:ℂ))*normDirichletSeries χ idealExponentNorm s := by
  rw [idealHeatTheta_scale A κ χ,mellin_comp_mul_right _ _ (one_div_pos.mpr hA),
    idealHeatTheta_one_mellin hκ χ hχ hs]
  have hp : ((1/A:ℝ):ℂ)^(-s) = (A:ℂ)^s := by
    simpa using mellin_scale_cpow zero_lt_one hA s
  rw [hp,smul_eq_mul,mul_assoc]

end CubicFirstMoment

end

end OAI
