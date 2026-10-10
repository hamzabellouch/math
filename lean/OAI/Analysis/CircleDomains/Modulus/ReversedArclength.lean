import OAI.Analysis.CircleDomains.Modulus.ReversedPhysicalLength
import OAI.Analysis.CircleDomains.Selection.ReversedResidualBounds
import OAI.Analysis.CircleDomains.Probability.PathOccupation

namespace OAI

/-! Reversing an ordinary rectifiable arc preserves its full occupation
measure, hence every measurable weighted arclength. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def reversedRectifiablePath (γ : RectifiablePath X) : RectifiablePath X :=
  ⟨reversedPath γ.val, by
    change eVariationOn (reversedPath γ.val) univ ≠ ∞
    rw [variation_reversedPath]
    exact γ.property⟩

theorem preimage_symm_Icc (a b : PathTime) :
    unitInterval.symm ⁻¹' Icc a b = Icc (unitInterval.symm b) (unitInterval.symm a) := by
  ext s
  simp only [mem_preimage, mem_Icc, unitInterval.le_symm_comm, unitInterval.symm_le_comm,
    and_comm]

theorem pathLengthMeasure_reversed (γ : RectifiablePath X) :
    pathLengthMeasure (reversedRectifiablePath γ) =
      (pathLengthMeasure γ).map unitInterval.symm := by
  apply Measure.ext_of_Icc
  intro a b hab
  rw [pathLengthMeasure_Icc _ hab,
    Measure.map_apply unitInterval.continuous_symm.measurable measurableSet_Icc,
    preimage_symm_Icc, pathLengthMeasure_Icc _ (unitInterval.symm_le_symm.mpr hab)]
  change eVariationOn (γ.val ∘ unitInterval.symm) (Icc a b) = _
  rw [eVariationOn.comp_eq_of_antitoneOn γ.val unitInterval.symm
    (unitInterval.strictAnti_symm.antitone.antitoneOn _), image_symm_Icc]

variable [MeasurableSpace X] [BorelSpace X]

theorem pathOccupation_reversed (γ : RectifiablePath X) :
    pathOccupation (reversedRectifiablePath γ) = pathOccupation γ := by
  rw [pathOccupation, pathLengthMeasure_reversed]
  change ((pathLengthMeasure γ).map unitInterval.symm).map (reversedPath γ.val) = _
  rw [Measure.map_map (reversedPath γ.val).continuous.measurable unitInterval.continuous_symm.measurable]
  change (pathLengthMeasure γ).map ((reversedPath γ.val) ∘ unitInterval.symm) = _
  have he : ((reversedPath γ.val) ∘ unitInterval.symm) = γ.val := by
    funext t
    change γ.val (unitInterval.symm (unitInterval.symm t)) = γ.val t
    rw [unitInterval.symm_symm]
  rw [he]
  rfl

end CircleDomainRigidity

end

end OAI
