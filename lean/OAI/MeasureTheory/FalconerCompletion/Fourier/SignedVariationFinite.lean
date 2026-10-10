import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Measures.SetToFunPostcompose

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CurrentFalconer.MonotoneShell
open MeasureTheory Set Filter PlanarFalconer
open scoped Topology ENNReal
instance signed_variation_finite (s : SignedMeasure ℝ) : IsFiniteMeasure s.variation := by
  rw [←s.totalVariation_eq_variation]
  infer_instance
lemma character_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℝ) :
    Integrable (fun x : ℝ => Complex.exp ((r:ℂ)*(x:ℂ)*Complex.I)) μ := by
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards with x
  simp [Complex.norm_exp,Complex.mul_re]
noncomputable def signedChar (s : SignedMeasure ℝ) (r : ℝ) : ℂ :=
  charFun s.toJordanDecomposition.posPart r-charFun s.toJordanDecomposition.negPart r
noncomputable def complexChar (ν : ComplexMeasure ℝ) (r : ℝ) : ℂ :=
  signedChar (ComplexMeasure.re ν) r+Complex.I*signedChar (ComplexMeasure.im ν) r
lemma signed_integral_character (s : SignedMeasure ℝ) (r : ℝ) :
    VectorMeasure.integral s (fun x : ℝ => Complex.exp ((r:ℂ)*(x:ℂ)*Complex.I))
      (ContinuousLinearMap.lsmul ℝ ℝ).flip = signedChar s r := by
  have he := s.toSignedMeasure_toJordanDecomposition
  have hp : s.toJordanDecomposition.posPart.toSignedMeasure.Integrable
      (fun x : ℝ => Complex.exp ((r:ℂ)*(x:ℂ)*Complex.I)) := by
    simpa only [VectorMeasure.Integrable,Measure.variation_toSignedMeasure] using
      character_integrable s.toJordanDecomposition.posPart r
  have hn : s.toJordanDecomposition.negPart.toSignedMeasure.Integrable
      (fun x : ℝ => Complex.exp ((r:ℂ)*(x:ℂ)*Complex.I)) := by
    simpa only [VectorMeasure.Integrable,Measure.variation_toSignedMeasure] using
      character_integrable s.toJordanDecomposition.negPart r
  change s.toJordanDecomposition.posPart.toSignedMeasure-s.toJordanDecomposition.negPart.toSignedMeasure = s at he
  calc
    _ = VectorMeasure.integral
        (s.toJordanDecomposition.posPart.toSignedMeasure-s.toJordanDecomposition.negPart.toSignedMeasure)
        (fun x : ℝ => Complex.exp ((r:ℂ)*(x:ℂ)*Complex.I)) (ContinuousLinearMap.lsmul ℝ ℝ).flip := congrArg (fun t : SignedMeasure ℝ => VectorMeasure.integral t
          (fun x : ℝ => Complex.exp ((r:ℂ)*(x:ℂ)*Complex.I)) (ContinuousLinearMap.lsmul ℝ ℝ).flip) he.symm
    _ = _ := by
      rw [VectorMeasure.integral_sub_vectorMeasure hp hn,
        VectorMeasure.integral_toSignedMeasure,VectorMeasure.integral_toSignedMeasure]
      simp only [signedChar,charFun_apply_real]
lemma complexChar_eq_fourier (ν : ComplexMeasure ℝ) (r : ℝ) : complexChar ν r = complexFourier ν (-r) := by
  have he : ν = (ComplexMeasure.re ν).toComplexMeasure 0 +
      (0:SignedMeasure ℝ).toComplexMeasure (ComplexMeasure.im ν) := by
    ext s
    change ν s = (⟨(ν s).re,0⟩:ℂ)+(⟨0,(ν s).im⟩:ℂ)
    apply Complex.ext <;> simp
  have hr : ((ComplexMeasure.re ν).toComplexMeasure 0).Integrable
      (fun x : ℝ => Complex.exp ((r:ℂ)*(x:ℂ)*Complex.I)) := by
    simpa only [VectorMeasure.Integrable,complexReal_variation] using
      character_integrable (ComplexMeasure.re ν).variation r
  have hi : ((0:SignedMeasure ℝ).toComplexMeasure (ComplexMeasure.im ν)).Integrable
      (fun x : ℝ => Complex.exp ((r:ℂ)*(x:ℂ)*Complex.I)) := by
    simpa only [VectorMeasure.Integrable,complexImag_variation] using
      character_integrable (ComplexMeasure.im ν).variation r
  have ht : (fun x : ℝ => Complex.exp (-(((-r:ℝ):ℂ)*(x:ℂ)*Complex.I))) =
      fun x : ℝ => Complex.exp ((r:ℂ)*(x:ℂ)*Complex.I) := by funext x;simp
  rw [complexFourier,ht]
  conv_rhs => rw [he,VectorMeasure.integral_add_vectorMeasure hr hi,
    complexReal_integral,complexImag_integral _ _ (character_integrable _ r),
    signed_integral_character,signed_integral_character]
  rfl
lemma complexChar_continuous (ν : ComplexMeasure ℝ) : Continuous (complexChar ν) := by
  unfold complexChar signedChar
  exact (continuous_charFun.sub continuous_charFun).add
    (continuous_const.mul (continuous_charFun.sub continuous_charFun))
lemma complexChar_positive (μ : FiniteMeasure ℝ) (r : ℝ) :
    complexChar (complexOfPositive μ) r = charFun (μ : Measure ℝ) r := by
  rw [complexChar_eq_fourier,complexFourier,complexOfPositive_integral,charFun_apply_real]
  congr 1
  funext x
  simp
lemma complexChar_sub (μ ν : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation] [IsFiniteMeasure ν.variation]
    (r : ℝ) : complexChar (μ-ν) r = complexChar μ r-complexChar ν r := by
  simp only [complexChar_eq_fourier,complexFourier]
  have ht : (fun x : ℝ => Complex.exp (-(((-r:ℝ):ℂ)*(x:ℂ)*Complex.I))) =
      fun x : ℝ => Complex.exp ((r:ℂ)*(x:ℂ)*Complex.I) := by funext x;simp
  rw [ht,VectorMeasure.integral_sub_vectorMeasure (character_integrable _ r) (character_integrable _ r)]
lemma real_variation_le (ν : ComplexMeasure ℝ) : (ComplexMeasure.re ν).variation ≤ ν.variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro s hs
  apply le_trans _ (ν.enorm_measure_le_variation s)
  change ‖(ν s).re‖ₑ ≤ ‖ν s‖ₑ
  rw [←ofReal_norm,←ofReal_norm,Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm (ν s))
lemma imag_variation_le (ν : ComplexMeasure ℝ) : (ComplexMeasure.im ν).variation ≤ ν.variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro s hs
  apply le_trans _ (ν.enorm_measure_le_variation s)
  change ‖(ν s).im‖ₑ ≤ ‖ν s‖ₑ
  rw [←ofReal_norm,←ofReal_norm,Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm (ν s))

end CurrentFalconer.MonotoneShell
end
end

end OAI
