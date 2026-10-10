import OAI.NumberTheory.DukePrimeDegree.Dynamics.VelocityClosedGraph
import OAI.NumberTheory.DukePrimeDegree.Geometry.CountableWeakKernel

namespace OAI

/-!
# Measurable distances to actual component velocity spaces

The lower semicontinuous distance on weak probabilities pulls back along
any genuine probability kernel. The measurable conclusion uses neither
a chosen tangent frame nor an added regularity assumption on the kernel.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Topology Matrix.Norms.Operator

namespace DukePrimeDegree
open PrimeDegreePackets

theorem measurable_kernel_velocityDistance
    {Z : Type*} [MeasurableSpace Z] (n : ℕ) [Nonempty (Fin n)]
    (κ : Kernel Z (X n)) [IsMarkovKernel κ]
    (V : Matrix (Fin n) (Fin n) ℝ) :
    Measurable (fun z => Metric.infDist V
      (matrixVelocitySpace (invariantRightSubgroup (κ z)))) := by
  let P : Z → ProbabilityMeasure (X n) := fun z => ⟨κ z, inferInstance⟩
  have hκ : @Measurable Z (ProbabilityMeasure (X n)) _
      (borel (ProbabilityMeasure (X n))) P :=
    measurable_kernel_probability_weak κ
  have hd : @Measurable (ProbabilityMeasure (X n)) ℝ
      (borel (ProbabilityMeasure (X n))) inferInstance
      (probabilityVelocityDistance n V) := by
    let : MeasurableSpace (ProbabilityMeasure (X n)) :=
      borel (ProbabilityMeasure (X n))
    let : BorelSpace (ProbabilityMeasure (X n)) := ⟨rfl⟩
    exact (lowerSemicontinuous_probabilityVelocityDistance n V).measurable
  have hm : Measurable (fun z => probabilityVelocityDistance n V (P z)) := hd.comp hκ
  simpa only [probabilityVelocityDistance, P, ProbabilityMeasure.coe_mk] using hm

end DukePrimeDegree

end

end OAI
