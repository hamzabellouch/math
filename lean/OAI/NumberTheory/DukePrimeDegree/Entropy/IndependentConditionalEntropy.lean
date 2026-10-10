import OAI.NumberTheory.DukePrimeDegree.Geometry.IndependentCoordinateKernel
import OAI.NumberTheory.PrimePackets.DisintegrationEntropy

namespace OAI

/-! # An independent neutral coordinate adds no conditional root information -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem independentCoordinate_conditionalEntropy
    {Z U V α : Type*} [MeasurableSpace Z] [MeasurableSpace U] [MeasurableSpace V]
    [StandardBorelSpace U] [Nonempty U] [Fintype α]
    (ρ : Measure (Z × U)) [IsFiniteMeasure ρ]
    (η : Measure V) [IsProbabilityMeasure η]
    (P : Z × U → α) (hP : ∀ a, MeasurableSet {z | P z=a}) :
    conditionalSigmaEntropy (independentCoordinateMeasure ρ η)
        (fun z => P (z.1.1,z.2))
        (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (Z × V))) =
      conditionalSigmaEntropy ρ P
        (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Z)) := by
  have hP' (a : α) : MeasurableSet {z : (Z × V) × U | P (z.1.1,z.2)=a} :=
    (hP a).preimage (measurable_fst.fst.prodMk measurable_snd)
  rw [conditionalSigmaEntropy_fst _ _ hP',conditionalSigmaEntropy_fst ρ P hP]
  have he : (fun z : Z × V => observationEntropy
      ((independentCoordinateMeasure ρ η).condKernel z) (fun u => P (z.1,u))) =ᵐ[
        (independentCoordinateMeasure ρ η).fst]
      (fun z => observationEntropy (ρ.condKernel z.1) (fun u => P (z.1,u))) := by
    filter_upwards [independentCoordinateMeasure_condKernel ρ η] with z hz
    rw [hz]
  rw [integral_congr_ae he,independentCoordinateMeasure_fst]
  have hmap : (ρ.fst.prod η).map Prod.fst=ρ.fst := by simp
  have hm := measurable_fiber_observationEntropy ρ.condKernel P hP
  have hI := integral_map (μ := ρ.fst.prod η) measurable_fst.aemeasurable
    hm.aestronglyMeasurable
  simpa only [hmap] using hI.symm

end DukePrimeDegree

end

end OAI
