import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Analytic.Constructions

namespace OAI

/-! The slit resolvent of a positive Hilbert-space contraction. This
common argument is used for the constant block and the full cusp operator;
it does not require compactness of the constant block. -/
noncomputable section
namespace CubicFirstMoment
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cubicThetaPositiveContraction_unit (G : H →L[ℂ] H)
    (hG : G.IsPositive) (hGnorm : ‖G‖ ≤ 1) {z : ℂ} (hz : z.im≠0 ∨ z.re<1) :
    IsUnit (1-z • G) := by
  by_cases hz0 : z=0
  · subst z
    have he : (0:ℂ) • G=0 := by ext F; simp
    rw [he,sub_zero]
    exact isUnit_one
  have hn : z⁻¹ ∉ spectrum ℂ (G) := by
    intro hm
    have hi : (z⁻¹).im=0 := hG.isSelfAdjoint.im_eq_zero_of_mem_spectrum hm
    have hr : 0 ≤ (z⁻¹).re := by
      apply SpectrumRestricts.nnreal_iff.mp hG.spectrumRestricts
      apply spectrum.of_algebraMap_mem (S:=ℂ)
      convert hm using 1
      exact (hG.isSelfAdjoint.mem_spectrum_eq_re hm).symm
    have hb : (z⁻¹).re ≤ 1 := by
      apply (Complex.re_le_norm _).trans
      apply (spectrum.norm_le_norm_mul_of_mem hm).trans
      exact (mul_le_mul hGnorm
        (ContinuousLinearMap.norm_id_le (𝕜:=ℂ) (E:=H))
        (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have he := congrArg Complex.re (mul_inv_cancel₀ hz0)
    have he' := congrArg Complex.im (mul_inv_cancel₀ hz0)
    simp only [Complex.mul_re,Complex.mul_im,hi,mul_zero,sub_zero,zero_add,Complex.one_re,Complex.one_im] at he he'
    rcases hz with hz | hz
    · have hzre : (z⁻¹).re=0 := (mul_eq_zero.mp he').resolve_left hz
      rw [hzre,mul_zero] at he
      exact zero_ne_one he
    · have hrpos : 0<(z⁻¹).re := lt_of_le_of_ne hr (by
        intro hh
        rw [← hh,mul_zero] at he
        exact zero_ne_one he)
      have hprod := mul_pos (sub_pos.mpr hz) hrpos
      nlinarith
  have hu := spectrum.notMem_iff.mp hn
  have hs := hu.smul (Units.mk0 z hz0)
  convert hs using 1
  all_goals
    simp [Units.smul_def,smul_sub,Algebra.algebraMap_eq_smul_one,smul_smul,hz0]


end CubicFirstMoment

end

end OAI
