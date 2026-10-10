import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Shells.ComplexOfPositive

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
namespace CurrentFalconer.MonotoneShell
open MeasureTheory Set Filter
open scoped Topology ENNReal
lemma setToFun_postcompose {μ : Measure ℝ} {T U : Set ℝ → ℂ →L[ℝ] ℂ} {C D : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) (hU : DominatedFinMeasAdditive μ U D)
    (L : ℂ →L[ℝ] ℂ) (he : ∀ s, U s = L.comp (T s))
    (f : ℝ → ℂ) (hf : Integrable f μ) :
    setToFun μ U hU f = L (setToFun μ T hT f) := by
  apply hf.induction (P := fun f => setToFun μ U hU f = L (setToFun μ T hT f))
  · intro c s hs hfin
    rw [setToFun_indicator_const hU hs hfin.ne,setToFun_indicator_const hT hs hfin.ne,he]
    rfl
  · intro f g hd hf hg hef heg
    rw [setToFun_add hU hf hg,setToFun_add hT hf hg,map_add,hef,heg]
  · exact isClosed_eq (continuous_setToFun hU) (L.continuous.comp (continuous_setToFun hT))
  · intro f g hfg hf heq
    rw [←setToFun_congr_ae hU hfg,←setToFun_congr_ae hT hfg,heq]
lemma complexReal_variation (s : SignedMeasure ℝ) : (s.toComplexMeasure 0).variation = s.variation := by
  unfold VectorMeasure.variation
  congr 1
  funext t
  change ‖((s t : ℝ):ℂ)‖ₑ = ‖s t‖ₑ
  simp only [enorm_eq_nnnorm,Complex.nnnorm_real]
lemma complexImag_variation (s : SignedMeasure ℝ) : ((0:SignedMeasure ℝ).toComplexMeasure s).variation = s.variation := by
  unfold VectorMeasure.variation
  congr 1
  funext t
  have he : ((0:SignedMeasure ℝ).toComplexMeasure s) t = (s t : ℂ)*Complex.I := by
    change (⟨0,s t⟩:ℂ) = (s t : ℂ)*Complex.I
    apply Complex.ext <;> simp
  rw [he,enorm_mul]
  simp only [enorm_eq_nnnorm,Complex.nnnorm_real,Complex.nnnorm_I,ENNReal.coe_one,mul_one]
lemma complexOfPositive_variation (μ : FiniteMeasure ℝ) : (complexOfPositive μ).variation = (μ : Measure ℝ) := by
  rw [complexOfPositive,complexReal_variation,Measure.variation_toSignedMeasure]
lemma complexReal_integral (s : SignedMeasure ℝ) (f : ℝ → ℂ) :
    VectorMeasure.integral (s.toComplexMeasure 0) f (ContinuousLinearMap.mul ℝ ℂ) =
      VectorMeasure.integral s f (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
  rw [VectorMeasure.integral_eq_setToFun,VectorMeasure.integral_eq_setToFun]
  simp only [complexReal_variation]
  apply setToFun_congr_left' _ _
  intro t ht hfin
  ext x
  simp only [VectorMeasure.transpose,VectorMeasure.mapRange_apply,
    LinearMap.toAddMonoidHom_coe,ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.flip_flip,ContinuousLinearMap.lsmul_apply]
  change x * (s t : ℂ) = (s t) • x
  simp [Complex.real_smul,mul_comm]
lemma complexImag_integral (s : SignedMeasure ℝ) (f : ℝ → ℂ) (hf : s.Integrable f) :
    VectorMeasure.integral ((0:SignedMeasure ℝ).toComplexMeasure s) f (ContinuousLinearMap.mul ℝ ℂ) =
      Complex.I * VectorMeasure.integral s f (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
  rw [VectorMeasure.integral_eq_setToFun,VectorMeasure.integral_eq_setToFun]
  simp only [complexImag_variation]
  apply setToFun_postcompose _ _ (ContinuousLinearMap.mul ℝ ℂ Complex.I) _ f hf
  intro t
  ext x
  simp only [VectorMeasure.transpose,VectorMeasure.mapRange_apply,
    ContinuousLinearMap.mul_apply',
    LinearMap.toAddMonoidHom_coe,ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.flip_flip,ContinuousLinearMap.lsmul_apply,
    ContinuousLinearMap.comp_apply]
  change x * (⟨0,s t⟩:ℂ) = Complex.I * ((s t) • x)
  have he : (⟨0,s t⟩:ℂ) = (s t : ℂ)*Complex.I := by apply Complex.ext <;> simp
  rw [he,Complex.real_smul]
  ring
lemma complexOfPositive_integral (μ : FiniteMeasure ℝ) (f : ℝ → ℂ) :
    VectorMeasure.integral (complexOfPositive μ) f (ContinuousLinearMap.mul ℝ ℂ) =
      ∫ x, f x ∂(μ : Measure ℝ) := by
  rw [complexOfPositive,complexReal_integral,VectorMeasure.integral_toSignedMeasure]

end CurrentFalconer.MonotoneShell
end
end

end OAI
