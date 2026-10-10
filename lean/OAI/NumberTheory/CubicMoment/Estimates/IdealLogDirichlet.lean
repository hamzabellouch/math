import OAI.NumberTheory.CubicMoment.Estimates.IdealDirichletHolomorphic
import OAI.NumberTheory.CubicMoment.Estimates.IdealVonMangoldt

namespace OAI

/-! Absolute convergence of the logarithmically weighted ideal series. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma summable_ideal_log_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun ν : EisensteinIdealExponent =>
      Real.log (idealExponentNorm ν)*idealExponentNorm ν^(-σ)) := by
  let ε : ℝ := (σ-1)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hmid : 1 < σ-ε := by dsimp [ε]; linarith
  apply ((summable_ideal_norm_rpow hmid).mul_left ε⁻¹).of_nonneg_of_le
    (fun ν => mul_nonneg (Real.log_nonneg (idealExponentNorm_ge_one ν))
      (Real.rpow_nonneg (idealExponentNorm_pos ν).le _))
  intro ν
  have hp := idealExponentNorm_pos ν
  have h := mul_le_mul_of_nonneg_right (Real.log_le_rpow_div hp.le hε)
    (Real.rpow_nonneg hp.le (-σ))
  calc
    _ ≤ (idealExponentNorm ν^ε/ε)*idealExponentNorm ν^(-σ) := h
    _ = ε⁻¹*idealExponentNorm ν^(-(σ-ε)) := by
      rw [div_eq_mul_inv]
      calc
        _ = ε⁻¹*(idealExponentNorm ν^ε*idealExponentNorm ν^(-σ)) := by ring
        _ = _ := by rw [←Real.rpow_add hp]; congr 2; ring

lemma idealLogDirichlet_norm_summable (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun ν => ‖(Real.log (idealExponentNorm ν):ℂ)*χ ν*
      (idealExponentNorm ν:ℂ)^(-s)‖) := by
  apply (summable_ideal_log_rpow hs).of_nonneg_of_le (fun _ => _root_.norm_nonneg _)
  intro ν
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (idealExponentNorm_ge_one ν)),
    Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),Complex.neg_re]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (Real.log_nonneg (idealExponentNorm_ge_one ν)) (hχ ν))
    (Real.rpow_nonneg (idealExponentNorm_pos ν).le _)

lemma idealVonMangoldtDirichlet_norm_summable (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun ν => ‖((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν*
      (idealExponentNorm ν:ℂ)^(-s)‖) := by
  apply (summable_ideal_log_rpow hs).of_nonneg_of_le (fun _ => _root_.norm_nonneg _)
  intro ν
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),Complex.neg_re]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_of_le_one_right (abs_nonneg _) (hχ ν)).trans (idealVonMangoldt_coeff_abs_le_logNorm ν))
    (Real.rpow_nonneg (idealExponentNorm_pos ν).le _)

end CubicFirstMoment

end

end OAI
