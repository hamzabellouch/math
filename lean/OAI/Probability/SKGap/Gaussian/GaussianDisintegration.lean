import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianRegression

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace SKGap.GaussianRegression

lemma residual_joint_gaussian {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] {P : Measure Ω} {X : Ω → ι → ℝ} {Y : Ω → κ → ℝ}
    (hXY : HasGaussianLaw (fun w => (X w,Y w)) P) (K : Matrix ι κ ℝ) :
    HasGaussianLaw (fun w => (X w-K*ᵥ Y w,Y w)) P :=
  hXY.map_fun (((ContinuousLinearMap.fst ℝ (ι → ℝ) (κ → ℝ))-
    (matrixCLM K).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ))).prod
    (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ)))

theorem regression_joint_law {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] {P : Measure Ω} {X : Ω → ι → ℝ} {Y : Ω → κ → ℝ}
    (hXY : HasGaussianLaw (fun w => (X w,Y w)) P) (K : Matrix ι κ ℝ)
    (hcov : ∀ i k, cov[fun w => X w i, fun w => Y w k; P] =
      ∑ l, K i l * cov[fun w => Y w l,fun w => Y w k; P]) :
    P.map (fun w => (X w,Y w)) =
      ((P.map (fun w => X w-K*ᵥ Y w)).prod (P.map Y)).map
        (fun z : (ι → ℝ) × (κ → ℝ) => (z.1+K*ᵥ z.2,z.2)) := by
  have := hXY.isProbabilityMeasure
  have hR := residual_joint_gaussian hXY K
  have hi := residual_independent hXY K hcov
  rw [← hi.map_prod_eq_prod_map_map hR.fst.aemeasurable hR.snd.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) hR.aemeasurable]
  congr 1
  funext w
  simp only [Function.comp_apply,sub_add_cancel]

theorem regression_lintegral {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] {P : Measure Ω} {X : Ω → ι → ℝ} {Y : Ω → κ → ℝ}
    (hXY : HasGaussianLaw (fun w => (X w,Y w)) P) (K : Matrix ι κ ℝ)
    (hcov : ∀ i k, cov[fun w => X w i, fun w => Y w k; P] =
      ∑ l, K i l * cov[fun w => Y w l,fun w => Y w k; P])
    (F : (ι → ℝ) × (κ → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F (X w,Y w) ∂P) =
      ∫⁻ y, ∫⁻ r, F (r+K*ᵥ y,y) ∂P.map (fun w => X w-K*ᵥ Y w) ∂P.map Y := by
  have := hXY.isProbabilityMeasure
  rw [← lintegral_map' hF.aemeasurable hXY.aemeasurable,
    regression_joint_law hXY K hcov,lintegral_map (by fun_prop) (by fun_prop),
    lintegral_prod_symm]
  fun_prop

end SKGap.GaussianRegression
end
end

end OAI
