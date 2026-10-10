import Mathlib
import OAI.Analysis.Conductivity.Sources.FaceMeasure

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
local instance sourceFaceIntegralCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance sourceFaceIntegralCircleIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma sourceFaceMeasure_le_cylinder {l r : ℝ} (hlr : l≤r) (i j : Fin 4) :
    sourceFaceMeasure l r i j ≤
      (volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2))) := by
  rw [sourceCylinderMeasure_eq_faces hlr]
  exact le_trans (Finset.single_le_sum (fun _ _ => Measure.zero_le _) (Finset.mem_univ j))
    (Finset.single_le_sum (f := fun face => ∑ patch,sourceFaceMeasure l r face patch)
      (fun _ _ => Measure.zero_le _) (Finset.mem_univ i))

lemma integrable_sourceFacePullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × UnitAddTorus (Fin 2) → E} {l r : ℝ} (hlr : l≤r)
    (hF : Integrable F ((volume.restrict (Ioc l r)).prod volume)) (i j : Fin 4) :
    IntegrableOn (fun x => sourceFaceWeight i j x • F (sourceFaceParameter i j x))
      (sourceExtendedBox l r) volume := by
  have hf := hF.mono_measure (sourceFaceMeasure_le_cylinder hlr i j)
  have hg := (integrable_map_measure hf.aestronglyMeasurable
    (continuous_sourceFaceParameter i j).aemeasurable).mp hf
  have hh := (integrable_withDensity_iff_integrable_smul'
    (continuous_sourceFaceWeight i j).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hg
  simpa only [IntegrableOn,Function.comp_apply,ENNReal.toReal_ofReal (sourceFaceWeight_pos i j _).le] using hh

theorem integral_sourceCylinder_faces {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × UnitAddTorus (Fin 2) → E} {l r : ℝ} (hlr : l≤r)
    (hF : Integrable F ((volume.restrict (Ioc l r)).prod volume)) :
    (∫ z,F z ∂(volume.restrict (Ioc l r)).prod volume)=
      ∑ i : Fin 4,∑ j : Fin 4,∫ x in sourceExtendedBox l r,
        sourceFaceWeight i j x • F (sourceFaceParameter i j x) := by
  have hf (i j : Fin 4) := hF.mono_measure (sourceFaceMeasure_le_cylinder hlr i j)
  rw [sourceCylinderMeasure_eq_faces hlr,integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.mpr (fun j _ => hf i j))]
  simp_rw [integral_finsetSum_measure (fun j _ => hf _ j)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact integral_sourceFaceMeasure l r i j (hf i j).aestronglyMeasurable

end ScalarConductivity

end
end

end OAI
