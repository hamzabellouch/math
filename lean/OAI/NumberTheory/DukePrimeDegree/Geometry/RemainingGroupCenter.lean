import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixBasedMeasure

namespace OAI

/-! # Centered Gaussian coordinates with values in the actual subgroup -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def remainingGroupCenter (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n) (t : c.Time) :
    c.Time ≃ₜ positiveRootGeneratedGroup (allPositiveRoots n \ P) :=
  (c.remainingWordHomeomorph hP hf).trans
    (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf t)⁻¹)

lemma remainingGroupCenter_image (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n) (t : c.Time) (U : Set c.Time) :
    c.remainingGroupCenter hP hf t '' U =
      (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf t)⁻¹) ''
        (c.remainingWordHomeomorph hP hf '' U) := by
  rw [image_image]
  rfl

lemma remainingGroupCenter_map (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n) (ν : Measure c.Time) (t : c.Time) :
    ν.map (c.remainingGroupCenter hP hf t) =
      c.remainingGroupLeafMeasure hP hf (c.centeredRemainingMeasure hP hf ν t) := by
  rw [c.groupLeafMeasure_centered]
  change _ = (ν.map (c.remainingWordHomeomorph hP hf)).map _
  rw [Measure.map_map (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf t)⁻¹).measurable
    (c.remainingWordHomeomorph hP hf).measurable]
  rfl

lemma basedRemainingGroupMeasure_eq_smul_center (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n)
    (ν : Measure c.Time) (t : c.Time) :
    c.remainingGroupLeafMeasure hP hf (c.basedRemainingMeasure hP hf ν t) =
      (c.centeredRemainingMeasure hP hf ν t (c.cube 1))⁻¹ •
        ν.map (c.remainingGroupCenter hP hf t) := by
  rw [c.remainingGroupCenter_map]
  change ((anchorNormalize (c.centeredRemainingMeasure hP hf ν t) (c.cube 1)).map
    (c.remainingWordHomeomorph hP hf)) = _
  rw [anchorNormalize,Measure.map_smul _ (c.remainingWordHomeomorph hP hf).measurable.aemeasurable]
  rfl

end EliminationChain
end DukePrimeDegree

end

end OAI
