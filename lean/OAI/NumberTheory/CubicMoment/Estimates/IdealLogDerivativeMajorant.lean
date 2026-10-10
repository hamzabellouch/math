import OAI.NumberTheory.CubicMoment.Estimates.IdealLogDerivativeTwist
import OAI.NumberTheory.CubicMoment.Estimates.PrincipalZetaLogDerivative

namespace OAI

/-! A uniform absolute bound on the right Mellin line. Positivity of the
actual von Mangoldt coefficients reduces every twist to the principal pole. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem idealLogDeriv_norm_le_principal
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    {L : ℂ → ℂ}
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    {σ t : ℝ} (hσ : 1 < σ) :
    ‖logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      (-logDeriv principalIdealZeta (σ:ℂ)).re := by
  have hst : 1 < ((σ:ℂ)+(t:ℂ)*Complex.I).re := by simpa using hσ
  have hsum := idealVonMangoldtDirichlet_norm_summable χ hχ hst
  have hp := idealMangoldt_real_hasSum (fun _ => 1) (by simp) hσ
  simp only [mul_one,Complex.one_re] at hp
  have hprincipal : (-logDeriv principalIdealZeta (σ:ℂ)).re=
      ∑' ν, (MvPowerSeries.coeff ν idealVonMangoldt:ℝ)*idealExponentNorm ν^(-σ) := by
    rw [idealSeries_logDeriv_eq (fun s hs => principalIdealZeta_right hs)
      (by simpa using hσ),idealDirichlet_neg_logDeriv (fun _ => 1)
        (by simp) (by simp) (by simp) (by simpa using hσ)]
    simpa only [mul_one] using hp.tsum_eq.symm
  rw [hprincipal,←norm_neg,idealSeries_logDeriv_eq hs hst,
    idealDirichlet_neg_logDeriv χ hχ hχ0 hχadd hst]
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum hp.summable
  intro ν
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (idealVonMangoldt_coeff_nonneg ν),
    Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),
    Complex.neg_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re]
  simp only [Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (idealVonMangoldt_coeff_nonneg ν) (hχ ν))
    (Real.rpow_nonneg (idealExponentNorm_pos ν).le _)

theorem idealLogDeriv_uniform_right_line :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (χ : EisensteinIdealExponent → ℂ), (∀ ν, ‖χ ν‖ ≤ 1) →
      χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
      ∀ (L : ℂ → ℂ),
      (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
      ∀ σ t : ℝ, 1 < σ → σ < 1+δ →
      ‖logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤ 1/(σ-1)+C := by
  obtain ⟨C,δ,hC,hδ,hb⟩ := principalIdealZeta_real_logDeriv_bound
  refine ⟨C,δ,hC,hδ,?_⟩
  intro χ hχ hχ0 hχadd L hs σ t hσ hσδ
  exact (idealLogDeriv_norm_le_principal χ hχ hχ0 hχadd hs hσ).trans (hb σ hσ hσδ)

end CubicFirstMoment

end

end OAI
