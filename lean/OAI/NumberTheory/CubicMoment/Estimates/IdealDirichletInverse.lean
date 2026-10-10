import OAI.NumberTheory.CubicMoment.Estimates.IdealMellinSeries
import OAI.NumberTheory.CubicMoment.Estimates.IdealMoebiusBounds

namespace OAI

/-! An absolutely convergent Möbius inverse of the complete ideal Hecke
series. In particular the actual series has no zeros to the right of one. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma ideal_cauchy_product (f g : EisensteinIdealExponent → ℂ)
    (hf : Summable (fun ν => ‖f ν‖)) (hg : Summable (fun ν => ‖g ν‖)) :
    (∑' ν, f ν)*(∑' ν, g ν)=
      ∑' ν, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν, f p.1*g p.2 := by
  have hpair : Summable (fun p : EisensteinIdealExponent × EisensteinIdealExponent =>
      f p.1*g p.2) := summable_mul_of_summable_norm hf hg
  exact Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (A := EisensteinIdealExponent) (f := f) (g := g) hf.of_norm hg.of_norm hpair

lemma idealDirichlet_norm_summable (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun ν => ‖χ ν*(idealExponentNorm ν:ℂ)^(-s)‖) := by
  simpa only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos _),
    Complex.neg_re] using summable_ideal_character_weight hs χ hχ

lemma idealDirichlet_weight_add (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) (s : ℂ) (ν κ : EisensteinIdealExponent) :
    χ (ν+κ)*(idealExponentNorm (ν+κ):ℂ)^(-s)=
      (χ ν*(idealExponentNorm ν:ℂ)^(-s))*(χ κ*(idealExponentNorm κ:ℂ)^(-s)) := by
  rw [hχ,idealExponentNorm_add,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (idealExponentNorm_pos ν).le (idealExponentNorm_pos κ).le]
  ring

lemma idealMoebius_antidiagonal (ν : EisensteinIdealExponent) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
      ((MvPowerSeries.coeff p.1 idealMoebiusSeries : ℝ) : ℂ)) = if ν=0 then 1 else 0 := by
  have h := congrArg (MvPowerSeries.coeff ν) idealMoebiusSeries_mul_zeta
  rw [MvPowerSeries.coeff_mul,MvPowerSeries.coeff_one] at h
  simp only [MvPowerSeries.coeff_apply,idealZeta,mul_one] at h
  simpa only [Complex.ofReal_sum,apply_ite,Complex.ofReal_one,
    Complex.ofReal_zero,MvPowerSeries.coeff_apply] using congrArg Complex.ofReal h

lemma idealMoebius_twist_summable (f : EisensteinIdealExponent → ℂ)
    (hf : Summable (fun ν => ‖f ν‖)) :
    Summable (fun ν => ‖((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)*f ν‖) := by
  apply hf.of_nonneg_of_le (fun _ => _root_.norm_nonneg _)
  intro ν
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_left (_root_.norm_nonneg _) (idealMoebiusSeries_abs_le_one ν)

lemma idealMoebius_twist_convolution (f : EisensteinIdealExponent → ℂ)
    (hf0 : f 0=1) (hfadd : ∀ ν κ, f (ν+κ)=f ν*f κ) (ν : EisensteinIdealExponent) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
      (((MvPowerSeries.coeff p.1 idealMoebiusSeries:ℝ):ℂ)*f p.1)*f p.2)=
        if ν=0 then 1 else 0 := by
  calc
    _ = (∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        ((MvPowerSeries.coeff p.1 idealMoebiusSeries:ℝ):ℂ))*f ν := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [mul_assoc,←hfadd,Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
    _ = _ := by
      rw [idealMoebius_antidiagonal]
      by_cases hν : ν=0
      · subst ν
        simp only [ite_true,one_mul,hf0]
      · simp only [hν,ite_false,zero_mul]

lemma idealMoebius_cauchy (f : EisensteinIdealExponent → ℂ)
    (hf : Summable (fun ν => ‖f ν‖)) :
    (∑' ν, ((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)*f ν)*(∑' ν, f ν)=
      ∑' ν, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        (((MvPowerSeries.coeff p.1 idealMoebiusSeries:ℝ):ℂ)*f p.1)*f p.2 := by
  have hg := idealMoebius_twist_summable f hf
  exact ideal_cauchy_product _ _ hg hf

lemma idealMoebius_tsum_mul (f : EisensteinIdealExponent → ℂ)
    (hf : Summable (fun ν => ‖f ν‖)) (hf0 : f 0=1)
    (hfadd : ∀ ν κ, f (ν+κ)=f ν*f κ) :
    (∑' ν, ((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)*f ν)*(∑' ν, f ν)=1 := by
  calc
    _ = ∑' ν, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        (((MvPowerSeries.coeff p.1 idealMoebiusSeries:ℝ):ℂ)*f p.1)*f p.2 := idealMoebius_cauchy f hf
    _ = ∑' ν : EisensteinIdealExponent, if ν=0 then (1:ℂ) else 0 :=
      tsum_congr (idealMoebius_twist_convolution f hf0 hfadd)
    _ = 1 := by simp only [tsum_ite_eq]

/-- The literal complete ideal series has its absolutely convergent
Möbius-twisted inverse on `Re(s)>1`. -/
theorem idealDirichlet_moebius_mul (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 1 < s.re) :
    normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)*χ ν)
      idealExponentNorm s * normDirichletSeries χ idealExponentNorm s = 1 := by
  have h0 : χ 0*(idealExponentNorm 0:ℂ)^(-s)=1 := by
    simp [hχ0,idealExponentNorm,idealExponentGenerator]
  have h := idealMoebius_tsum_mul (fun ν => χ ν*(idealExponentNorm ν:ℂ)^(-s))
    (idealDirichlet_norm_summable χ hχ hs) h0 (idealDirichlet_weight_add χ hχadd s)
  simpa only [normDirichletSeries,mul_assoc] using h

theorem idealDirichlet_ne_zero (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 1 < s.re) :
    normDirichletSeries χ idealExponentNorm s ≠ 0 := by
  intro hzero
  have h := idealDirichlet_moebius_mul χ hχ hχ0 hχadd hs
  rw [hzero,mul_zero] at h
  exact zero_ne_one h

end CubicFirstMoment

end

end OAI
