import OAI.Analysis.FiniteFactor.OrbitSampling.Cube
import Mathlib.Topology.Instances.Rat

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

/-- Finite cylinders in the full real product: coordinates outside the
finite support are unrestricted. On the conull cube these are the original
rational tests. The ambient real product is not asserted to be compact. -/
def sourceSamplingCylinder (T : SourceSamplingRationalTest) : Set SourceSamplingPair :=
  {p | ∀ i ∈ T.1, p.1 i ∈ sourceSamplingRationalX T i ∧ p.2 i ∈ sourceSamplingRationalY T i}

theorem sourceSamplingCylinder_measurable (T : SourceSamplingRationalTest) :
    MeasurableSet (sourceSamplingCylinder T) := by
  simp only [sourceSamplingCylinder,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    (measurableSet_Icc.preimage ((measurable_pi_apply i).comp measurable_fst)).inter
    (measurableSet_Icc.preimage ((measurable_pi_apply i).comp measurable_snd))))

theorem sourceSamplingCylinder_on_cube (T : SourceSamplingRationalTest) (p : SourceSamplingPair)
    (hp : p ∈ sourceSamplingCube) :
    p ∈ sourceSamplingCylinder T ↔
    p ∈ sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T) := by
  constructor
  · intro h i
    by_cases hi : i ∈ T.1
    · exact h i hi
    · simpa [sourceSamplingRationalX,sourceSamplingRationalY,sourceSamplingRationalEndpoints,hi]
        using hp i
  · intro h i _
    exact h i

def sourceSamplingTestMeet (T U : SourceSamplingRationalTest) : SourceSamplingRationalTest :=
  ⟨T.1 ∪ U.1,fun i =>
    if i.1 ∈ T.1 then
      if i.1 ∈ U.1 then
        ((max (sourceSamplingRationalEndpoints T i).1.1 (sourceSamplingRationalEndpoints U i).1.1,
          min (sourceSamplingRationalEndpoints T i).1.2 (sourceSamplingRationalEndpoints U i).1.2),
         (max (sourceSamplingRationalEndpoints T i).2.1 (sourceSamplingRationalEndpoints U i).2.1,
          min (sourceSamplingRationalEndpoints T i).2.2 (sourceSamplingRationalEndpoints U i).2.2))
      else sourceSamplingRationalEndpoints T i
    else sourceSamplingRationalEndpoints U i⟩

theorem sourceSamplingCylinder_inter (T U : SourceSamplingRationalTest) :
    sourceSamplingCylinder (sourceSamplingTestMeet T U) =
      sourceSamplingCylinder T ∩ sourceSamplingCylinder U := by
  have hcoord (p : SourceSamplingPair) (i : SourceCoordinate) :
      (i ∈ T.1 ∪ U.1 → p.1 i ∈ sourceSamplingRationalX (sourceSamplingTestMeet T U) i ∧
        p.2 i ∈ sourceSamplingRationalY (sourceSamplingTestMeet T U) i) ↔
      (i ∈ T.1 → p.1 i ∈ sourceSamplingRationalX T i ∧ p.2 i ∈ sourceSamplingRationalY T i) ∧
      (i ∈ U.1 → p.1 i ∈ sourceSamplingRationalX U i ∧ p.2 i ∈ sourceSamplingRationalY U i) := by
    by_cases ht : i ∈ T.1 <;> by_cases hu : i ∈ U.1 <;>
      simp [sourceSamplingRationalX,sourceSamplingRationalY,sourceSamplingRationalEndpoints,
        sourceSamplingTestMeet,ht,hu,Set.mem_Icc]
    tauto
  ext p
  change (∀ i, i ∈ T.1 ∪ U.1 → _) ↔ (∀ i, i ∈ T.1 → _) ∧ (∀ i, i ∈ U.1 → _)
  constructor
  · intro h
    exact ⟨fun i => ((hcoord p i).mp (h i)).1,fun i => ((hcoord p i).mp (h i)).2⟩
  · rintro ⟨hT,hU⟩ i
    exact (hcoord p i).mpr ⟨hT i,hU i⟩

theorem sourceSamplingCylinder_piSystem : IsPiSystem (Set.range sourceSamplingCylinder) := by
  rintro _ ⟨T,rfl⟩ _ ⟨U,rfl⟩ _
  exact ⟨sourceSamplingTestMeet T U,sourceSamplingCylinder_inter T U⟩

end
end FiniteFactor

end OAI
