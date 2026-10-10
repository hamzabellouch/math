import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.Basic
import OAI.Probability.SKBarriers.Gaussian.ExponentialGrowth

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section RawDerivatives
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ E] in
theorem HasExpGrowth.clm {f : E → F} (hg : HasExpGrowth f) (L : F →L[ℝ] G) :
    HasExpGrowth (fun x => L (f x)) :=
  hg.congr_bound (norm_nonneg L) (fun x => L.le_opNorm (f x))

theorem contDiff_two_gaussian_integral_fderiv
    (f : E × ℝ → F) (hf : ContDiff ℝ 2 f)
    (hg : HasExpGrowth f) (hg₁ : HasExpGrowth (fderiv ℝ f))
    (hg₂ : HasExpGrowth (fderiv ℝ (fderiv ℝ f))) :
    ContDiff ℝ 2 (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  let L := ContinuousLinearMap.inl ℝ E ℝ
  let T := (ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip L
  let T₁ := (ContinuousLinearMap.compL ℝ E (E × ℝ) (E →L[ℝ] F)).flip L
  let f₁ : E × ℝ → E →L[ℝ] F := fun z => T (fderiv ℝ f z)
  let S := (ContinuousLinearMap.compL ℝ (E × ℝ) ((E × ℝ) →L[ℝ] F) (E →L[ℝ] F)) T
  let f₂ : E × ℝ → E →L[ℝ] E →L[ℝ] F := fun z => T₁ (S (fderiv ℝ (fderiv ℝ f) z))
  have hf₁ : ContDiff ℝ 1 f₁ := T.contDiff.comp (hf.fderiv_right (by norm_num))
  have hf₂ : Continuous f₂ := T₁.continuous.comp (S.continuous.comp
    ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).fderiv_right (m := 0) (by norm_num)).continuous)
  have hg₂T : HasExpGrowth f₂ := by
    obtain ⟨C,M,hC,hM,hg₂⟩ := hg₂
    refine ⟨‖T₁‖*‖S‖*C,M,mul_nonneg (mul_nonneg (norm_nonneg T₁) (norm_nonneg S)) hC,hM,?_⟩
    intro z
    calc
      ‖f₂ z‖ ≤ ‖T₁‖ * ‖S (fderiv ℝ (fderiv ℝ f) z)‖ := T₁.le_opNorm _
      _ ≤ ‖T₁‖ * (‖S‖ * ‖fderiv ℝ (fderiv ℝ f) z‖) :=
        mul_le_mul_of_nonneg_left (S.le_opNorm _) (norm_nonneg _)
      _ ≤ ‖T₁‖ * (‖S‖ * (C * Real.exp (M * ‖z‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hg₂ z) (norm_nonneg S)) (norm_nonneg _)
      _ = _ := by ring
  apply contDiff_two_gaussian_integral f f₁ f₂ hf.continuous hf₁.continuous hf₂ hg
    (hg₁.clm T) hg₂T
  · intro x y
    exact (hf.differentiable (by norm_num) (x,y)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))
  · intro x y
    have hd := T.hasFDerivAt.comp (x,y)
      ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).differentiable (by norm_num) (x,y)).hasFDerivAt
    have hxy : HasFDerivAt (fun z : E => (z,y)) L x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const y x)
    convert! hd.comp x hxy using 1

end RawDerivatives
end SK.Analytic

end
end
end
end
end
end

end OAI
