import OAI.NumberTheory.CubicMoment.Estimates.IdealLogDirichlet
import Mathlib.Analysis.Calculus.LogDeriv

namespace OAI

/-! The logarithmic derivative of the complete ideal series is the
actual ideal von Mangoldt Dirichlet series on `Re(s)>1`. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealVonMangoldt_antidiagonal (ν : EisensteinIdealExponent) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
      ((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ))=(Real.log (idealExponentNorm ν):ℂ) := by
  have h := congrArg (MvPowerSeries.coeff ν) idealZeta_mul_vonMangoldt
  rw [MvPowerSeries.coeff_mul] at h
  simp only [MvPowerSeries.coeff_apply,idealZeta,one_mul,idealLogNorm] at h
  simpa only [Complex.ofReal_sum,MvPowerSeries.coeff_apply] using congrArg Complex.ofReal h

lemma idealVonMangoldt_twist_convolution (f : EisensteinIdealExponent → ℂ)
    (hfadd : ∀ ν κ, f (ν+κ)=f ν*f κ) (ν : EisensteinIdealExponent) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
      f p.1*(((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ)*f p.2))=
        (Real.log (idealExponentNorm ν):ℂ)*f ν := by
  calc
    _ = (∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        ((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ))*f ν := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [show f p.1*(((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ)*f p.2)=
          ((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ)*(f p.1*f p.2) by ring,
        ←hfadd,Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
    _ = _ := by rw [idealVonMangoldt_antidiagonal]

lemma idealVonMangoldt_tsum_mul (f : EisensteinIdealExponent → ℂ)
    (hf : Summable (fun ν => ‖f ν‖))
    (hg : Summable (fun ν => ‖((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*f ν‖))
    (hfadd : ∀ ν κ, f (ν+κ)=f ν*f κ) :
    (∑' ν, f ν)*(∑' ν, ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*f ν)=
      ∑' ν, (Real.log (idealExponentNorm ν):ℂ)*f ν := by
  calc
    _ = ∑' ν, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        f p.1*(((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ)*f p.2) :=
      ideal_cauchy_product _ _ hf hg
    _ = _ := tsum_congr (idealVonMangoldt_twist_convolution f hfadd)

theorem idealDirichlet_neg_logDeriv (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (normDirichletSeries χ idealExponentNorm) s=
      normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν)
        idealExponentNorm s := by
  have hM := idealVonMangoldt_tsum_mul (fun ν => χ ν*(idealExponentNorm ν:ℂ)^(-s))
    (idealDirichlet_norm_summable χ hχ hs)
    (by simpa only [mul_assoc] using idealVonMangoldtDirichlet_norm_summable χ hχ hs)
    (idealDirichlet_weight_add χ hχadd s)
  have hD := (idealDirichlet_hasSum_deriv χ hχ hs).tsum_eq
  have hlog : deriv (normDirichletSeries χ idealExponentNorm) s=
      -(∑' ν, (Real.log (idealExponentNorm ν):ℂ)*(χ ν*(idealExponentNorm ν:ℂ)^(-s))) := by
    rw [←hD,←tsum_neg]
    apply tsum_congr
    intro ν
    ring
  have hn := idealDirichlet_ne_zero χ hχ hχ0 hχadd hs
  rw [logDeriv_apply,hlog,neg_div,neg_neg,div_eq_iff hn]
  simpa only [normDirichletSeries,mul_assoc,mul_comm,mul_left_comm] using hM.symm

end CubicFirstMoment

end

end OAI
