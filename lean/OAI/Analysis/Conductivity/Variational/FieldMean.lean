import Mathlib
import OAI.Analysis.Conductivity.Variational.SmoothDirectionIntegral
import OAI.Analysis.Conductivity.Variational.FieldVectorCLM

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped ENNReal Matrix.Norms.Elementwise

lemma integral_fieldVector_eq_zero
    (μ : Measure Coord3) [IsFiniteMeasureOnCompacts μ]
    (F : Coord3 → Matrix (Fin 3) (Fin 2) ℝ)
    (hF : Continuous F) (hc : HasCompactSupport F)
    (hmean : ∀ i j, (∫ x, F x i j ∂μ) = 0) :
    (∫ x, fieldVector (F x) ∂μ) = 0 := by
  have hi : Integrable (fun x => fieldVector (F x)) μ :=
    (fieldVectorCLM.continuous.comp hF).integrable_of_hasCompactSupport
      (hc.comp_left (map_zero fieldVectorCLM))
  ext ij
  have h := (EuclideanSpace.proj ij).integral_comp_comm hi
  exact h.symm.trans (hmean ij.1 ij.2)

lemma voltageGradient_mean_zero
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {u : Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u) (hc : HasCompactSupport u) :
    (∫ x, voltageGradient u x ∂μ) = 0 := by
  have hi : Integrable (voltageGradient u) μ :=
    (continuous_voltageGradient hu).integrable_of_hasCompactSupport (compact_voltageGradient hc)
  ext ij
  have h := (EuclideanSpace.proj ij).integral_comp_comm hi
  change (EuclideanSpace.proj ij) (∫ x, voltageGradient u x ∂μ) = 0
  rw [← h]
  let v : Coord3 := Pi.single ij.1 1
  let f : SmoothScalar Coord3 := ⟨fun x => u x ij.2, (contDiff_apply ℝ ℝ ij.2).comp hu⟩
  have hf : HasCompactSupport f.val := hc.comp_left (g := fun w : Fin 2 → ℝ => w ij.2) rfl
  have hm := smooth_direction_integral_zero μ v f hf
  convert hm using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    have hd : fderiv ℝ f.val x = (ContinuousLinearMap.proj ij.2).comp (fderiv ℝ u x) :=
      ((ContinuousLinearMap.proj ij.2 : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp x
        (hu.differentiable (by simp) x).hasFDerivAt).fderiv
    change (gradientColumns (fderiv ℝ u x)) ij.1 ij.2 = fderiv ℝ f.val x v
    rw [hd]
    simp only [gradientColumns,transpose_apply,LinearMap.toMatrix'_apply,
      ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
    rfl

lemma CompactGlobalUpdate.flux_mean_zero
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) :
    (∫ x, fieldVector (R.dF x) ∂μ) = 0 := by
  apply integral_fieldVector_eq_zero μ R.dF R.smooth_dF.continuous R.compact_dF
  intro i j
  exact compact_flux_mean_zero μ (fun x => (R.dF x).col j) (R.cauchy_dF j) i

end ScalarConductivity

end
end

end OAI
