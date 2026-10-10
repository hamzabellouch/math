import Mathlib
import OAI.Analysis.Conductivity.Variational.FieldVectorCLM

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology Matrix
open scoped ENNReal NNReal

lemma gradientVectorCLM_injective : Function.Injective gradientVectorCLM := by
  intro D E h
  have hm : gradientColumns D = gradientColumns E := by
    ext i j
    exact congrArg (fun v : FieldVector => v (i,j)) h
  ext v j
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 2) ℝ => (Mᵀ *ᵥ v) j) hm
  simpa only [gradientColumns_apply] using h

lemma exists_gradientCoordinateConstant :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ D : Coord3 →L[ℝ] (Fin 2 → ℝ),
      ‖D‖ ≤ K * ‖gradientVectorCLM D‖ := by
  obtain ⟨K,hK,hbound⟩ := gradientVectorCLM.toLinearMap.injective_iff_antilipschitz.mp
    gradientVectorCLM_injective
  refine ⟨K,hK,fun D => ?_⟩
  simpa only [dist_zero_right,map_zero,ContinuousLinearMap.coe_coe] using hbound.le_mul_dist D 0

def gradientCoordinateConstant : ℝ≥0 := exists_gradientCoordinateConstant.choose

lemma gradientCoordinateConstant_bound (D : Coord3 →L[ℝ] (Fin 2 → ℝ)) :
    ‖D‖ ≤ gradientCoordinateConstant * ‖gradientVectorCLM D‖ :=
  exists_gradientCoordinateConstant.choose_spec.2 D

lemma compact_voltage_poincare
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUb : Bornology.IsBounded U)
    {v : Coord3 → Fin 2 → ℝ} (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (hvc : HasCompactSupport v) (hvs : tsupport v ⊆ U) :
    (eLpNorm v 2 (μ.restrict U)).toReal ≤
      (eLpNormLESNormFDerivOfLeConst (Fin 2 → ℝ) μ U 2 2 *
        gradientCoordinateConstant : ℝ≥0) *
      (eLpNorm (voltageGradient v) 2 (μ.restrict U)).toReal := by
  have hvm : MemLp (voltageGradient v) 2 μ := memLp_voltageGradient_smooth_compact μ hv hvc
  have he := eLpNorm_le_eLpNorm_fderiv μ
    (hv.of_le (by simp) : ContDiff ℝ 1 v) ((subset_tsupport v).trans hvs)
    (p := 2) (by norm_num) (by norm_num [Coord3,Module.finrank_pi]) hUb
  have hder : eLpNorm (fderiv ℝ v) 2 μ ≤
      gradientCoordinateConstant * eLpNorm (voltageGradient v) 2 μ :=
    eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      (hv.continuous_fderiv (by simp)).aestronglyMeasurable
      (Eventually.of_forall fun point => by
        exact_mod_cast gradientCoordinateConstant_bound (fderiv ℝ v point)) 2
  have hall : eLpNorm v 2 μ ≤
      (eLpNormLESNormFDerivOfLeConst (Fin 2 → ℝ) μ U 2 2 : ℝ≥0∞) *
      (gradientCoordinateConstant * eLpNorm (voltageGradient v) 2 μ) := by
    exact he.trans (mul_le_mul le_rfl hder (by positivity) (by positivity))
  have hfin : (eLpNormLESNormFDerivOfLeConst (Fin 2 → ℝ) μ U 2 2 : ℝ≥0∞) *
      (gradientCoordinateConstant * eLpNorm (voltageGradient v) 2 μ) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hvm.eLpNorm_ne_top)
  have ht := ENNReal.toReal_mono hfin hall
  rw [eLpNorm_restrict_eq_of_support_subset hv.continuous.aestronglyMeasurable
      ((subset_tsupport v).trans hvs),
    eLpNorm_restrict_eq_of_support_subset hvm.aestronglyMeasurable
      ((subset_tsupport _).trans (tsupport_voltageGradient.trans hvs))]
  simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal,NNReal.coe_mul,mul_assoc] using ht

end ScalarConductivity

end
end

end OAI
