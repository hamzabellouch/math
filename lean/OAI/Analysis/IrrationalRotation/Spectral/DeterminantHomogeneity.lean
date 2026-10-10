import OAI.Analysis.IrrationalRotation.Spectral.SpectralNaturality
import OAI.Analysis.IrrationalRotation.Model.ConcreteSpectral

namespace OAI

noncomputable section
open scoped ENNReal CStarAlgebra
namespace Invariant233

def positiveRegularizerScale (r : ℝ) (hr : 0 < r) :
    {ε : ℝ // 0 < ε} ≃ {ε : ℝ // 0 < ε} where
  toFun ε := ⟨r * ε.val, mul_pos hr ε.property⟩
  invFun ε := ⟨ε.val / r, div_pos ε.property hr⟩
  left_inv ε := by apply Subtype.ext; dsimp; field_simp [ne_of_gt hr]
  right_inv ε := by apply Subtype.ext; dsimp; field_simp [ne_of_gt hr]

section CStar
variable {A : Type*} [CStarAlgebra A]

theorem star_smul_mul_smul (z : ℂ) (a : A) :
    star (z • a) * (z • a) = ‖z‖ ^ 2 • (star a * a) := by
  rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [show star z * z = (‖z‖ ^ 2 : ℝ) by
    simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.conj_mul' z]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

theorem regularizedLog_smul (z : ℂ) (hz : z ≠ 0) (a : A) (ε : ℝ) (hε : 0 < ε) :
    CFC.log (star (z • a) * (z • a) + (‖z‖ ^ 2 * ε) • (1 : A)) =
      algebraMap ℝ A (2 * Real.log ‖z‖) +
        CFC.log (star a * a + ε • (1 : A)) := by
  rw [star_smul_mul_smul, mul_smul, ← smul_add]
  rw [CFC.log_smul _ (fun x hx => ne_of_gt (regularizedNormSquare_spectrum_pos a ε hε x hx))
    (pow_ne_zero _ (norm_ne_zero_iff.mpr hz)) (by simp [IsSelfAdjoint])]
  rw [Real.log_pow]
  norm_num

theorem fugledeKadisonDeterminant_smul (τ : TracialState A) (z : ℂ) (a : A) :
    fugledeKadisonDeterminant τ (z • a) =
      ENNReal.ofReal ‖z‖ * fugledeKadisonDeterminant τ a := by
  by_cases hz : z = 0
  · subst z
    simp [fugledeKadisonDeterminant_zero]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  unfold fugledeKadisonDeterminant
  rw [← (positiveRegularizerScale (‖z‖ ^ 2) (sq_pos_of_pos hn)).iInf_comp]
  rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_ne_zero_iff.mpr hn) ENNReal.ofReal_ne_top]
  apply iInf_congr
  intro ε
  change ENNReal.ofReal (Real.exp ((τ (CFC.log
    (star (z • a) * (z • a) + (‖z‖ ^ 2 * ε.val) • (1 : A)))).re / 2)) = _
  rw [regularizedLog_smul z hz a ε.val ε.property]
  rw [map_add, TracialState.map_real]
  simp only [Complex.add_re, Complex.ofReal_re]
  rw [show (2 * Real.log ‖z‖ + (τ (CFC.log (star a * a + ε.val • (1 : A)))).re) / 2 =
      Real.log ‖z‖ + (τ (CFC.log (star a * a + ε.val • (1 : A)))).re / 2 by ring]
  rw [Real.exp_add, Real.exp_log hn, ENNReal.ofReal_mul hn.le]

end CStar

section Vector
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in

theorem vectorTrace_real_scalar (ξ : H) (hξ : ‖ξ‖ = 1) (r : ℝ) :
    vectorTrace ξ (algebraMap ℝ (H →L[ℂ] H) r) = (r : ℂ) := by
  simp [vectorTrace, Algebra.algebraMap_eq_smul_one, inner_smul_right_eq_smul,
    inner_self_eq_norm_sq_to_K, hξ, Complex.real_smul]

theorem vectorFugledeKadisonDeterminant_zero (ξ : H) (hξ : ‖ξ‖ = 1) :
    vectorFugledeKadisonDeterminant ξ 0 = 0 := by
  unfold vectorFugledeKadisonDeterminant
  simp only [star_zero, zero_mul, zero_add, ← Algebra.algebraMap_eq_smul_one,
    CFC.log_algebraMap, vectorTrace_real_scalar ξ hξ, Complex.ofReal_re]
  have h : ∀ ε : {r : ℝ // 0 < r},
      Real.exp (Real.log ε.val / 2) = Real.sqrt ε.val :=
    fun ε => exp_half_log_eq_sqrt ε.property
  simp_rw [h]
  simpa using iInf_sqrt_sq_add_pos 0 le_rfl

theorem vectorFugledeKadisonDeterminant_smul (ξ : H) (hξ : ‖ξ‖ = 1)
    (z : ℂ) (T : H →L[ℂ] H) :
    vectorFugledeKadisonDeterminant ξ (z • T) =
      ENNReal.ofReal ‖z‖ * vectorFugledeKadisonDeterminant ξ T := by
  by_cases hz : z = 0
  · subst z
    simp [vectorFugledeKadisonDeterminant_zero ξ hξ]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  unfold vectorFugledeKadisonDeterminant
  rw [← (positiveRegularizerScale (‖z‖ ^ 2) (sq_pos_of_pos hn)).iInf_comp]
  rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_ne_zero_iff.mpr hn) ENNReal.ofReal_ne_top]
  apply iInf_congr
  intro ε
  change ENNReal.ofReal (Real.exp ((vectorTrace ξ (CFC.log
    (star (z • T) * (z • T) + (‖z‖ ^ 2 * ε.val) • (1 : H →L[ℂ] H)))).re / 2)) = _
  rw [regularizedLog_smul z hz T ε.val ε.property]
  have hadd (A B : H →L[ℂ] H) : vectorTrace ξ (A + B) = vectorTrace ξ A + vectorTrace ξ B := by
    simp [vectorTrace, inner_add_right]
  rw [hadd, vectorTrace_real_scalar ξ hξ]
  simp only [Complex.add_re, Complex.ofReal_re]
  rw [show (2 * Real.log ‖z‖ + (vectorTrace ξ (CFC.log (star T * T + ε.val • (1 : H →L[ℂ] H)))).re) / 2 =
      Real.log ‖z‖ + (vectorTrace ξ (CFC.log (star T * T + ε.val • (1 : H →L[ℂ] H)))).re / 2 by ring]
  rw [Real.exp_add, Real.exp_log hn, ENNReal.ofReal_mul hn.le]

end Vector
end Invariant233

end

end OAI
