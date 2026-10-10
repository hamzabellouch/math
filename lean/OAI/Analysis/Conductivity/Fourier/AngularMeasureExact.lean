import Mathlib
import OAI.Analysis.Conductivity.Sources.AngularGraph

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

def faceRayMeasure (w : ℝ) (j : Fin 4) : Measure UnitAddCircle :=
  Measure.map (fun b : ℝ => ((faceRayAngle w j b:ℝ):UnitAddCircle))
    ((volume.restrict (Ioc (-1:ℝ) 1)).withDensity (fun b => ENNReal.ofReal (faceRayDensity w j b)))

lemma continuous_faceRayCircle (w : ℝ) (j : Fin 4) :
    Continuous (fun b : ℝ => ((faceRayAngle w j b:ℝ):UnitAddCircle)) :=
  (AddCircle.continuous_mk' 1).comp
    (continuous_iff_continuousAt.mpr fun b => (hasDerivAt_faceRayAngle w j b).continuousAt)

instance finite_faceRayMeasure (w : ℝ) (j : Fin 4) : IsFiniteMeasure (faceRayMeasure w j) := by
  have h : IntegrableOn (faceRayDensity w j) (Icc (-1:ℝ) 1) volume :=
    (continuous_faceRayDensity w j).continuousOn.integrableOn_compact
    (isCompact_Icc (a:=(-1:ℝ)) (b:=1))
  have := isFiniteMeasure_withDensity_ofReal (h.mono_set Ioc_subset_Icc_self).hasFiniteIntegral
  unfold faceRayMeasure
  infer_instance

lemma integral_faceRayMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : ℝ} (hw : 0<w) (j : Fin 4) {F : UnitAddCircle → E}
    (hF : AEStronglyMeasurable F (faceRayMeasure w j)) :
    (∫ θ,F θ ∂faceRayMeasure w j)=
      ∫ b in Ioc (-1:ℝ) 1,faceRayDensity w j b • F ((faceRayAngle w j b:ℝ):UnitAddCircle) := by
  rw [faceRayMeasure,integral_map (continuous_faceRayCircle w j).measurable.aemeasurable hF]
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_faceRayDensity w j).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun b => ENNReal.ofReal_lt_top)]
  congr 1
  funext b
  rw [ENNReal.toReal_ofReal (faceRayDensity_pos' hw j b).le]

theorem haar_circle_eq_sum_faceRayMeasure {w : ℝ} (hw : 0<w) :
    AddCircle.haarAddCircle=∑ j : Fin 4,faceRayMeasure w j := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro F
  rw [integral_finsetSum_measure]
  · rw [integral_circle_faces (F := fun θ => F θ) hw F.continuous]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_faceRayMeasure (F := fun θ => F θ) hw j F.continuous.aestronglyMeasurable]
    rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1)]
    apply integral_congr_ae
    filter_upwards [] with b
    simp only [smul_eq_mul,mul_comm]
  · intro j _
    exact F.integrable

theorem integral_circle_faces_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {w : ℝ} (hw : 0<w) {F : UnitAddCircle → E}
    (hF : Integrable F AddCircle.haarAddCircle) :
    (∫ θ,F θ ∂AddCircle.haarAddCircle)=
      ∑ j : Fin 4, ∫ b in Ioc (-1:ℝ) 1,
        faceRayDensity w j b • F ((faceRayAngle w j b:ℝ):UnitAddCircle) := by
  have hsum : Integrable F (∑ j : Fin 4,faceRayMeasure w j) := by
    rwa [←haar_circle_eq_sum_faceRayMeasure hw]
  have hint (j : Fin 4) : Integrable F (faceRayMeasure w j) :=
    hsum.mono_measure (Finset.single_le_sum (fun _ _ => Measure.zero_le _) (Finset.mem_univ j))
  rw [haar_circle_eq_sum_faceRayMeasure hw,integral_finsetSum_measure (fun j _ => hint j)]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_faceRayMeasure hw j (hint j).aestronglyMeasurable

end ScalarConductivity

end
end

end OAI
