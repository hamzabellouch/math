import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootLeafKernel
import OAI.NumberTheory.PrimePackets.DisintegrationEntropy

namespace OAI

/-! # Actual conditional information on full upper-root leaves -/

noncomputable section
open MeasureTheory Filter Set

namespace DukePrimeDegree
open PrimeDegreePackets
namespace UpperRootBox

variable {n : ℕ} {g : G n} {α : Type*} [Fintype α]

theorem conditionalEntropy_eq_leafMeasure (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (P : UpperRootTransverse n × UpperRootTime n → α)
    (hP : ∀ a, MeasurableSet {z | P z = a}) :
    conditionalSigmaEntropy (A.coordinateMeasure μ) P
        (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (UpperRootTransverse n))) =
      ∫ s, observationEntropy ((A.leafMeasure R μ s).restrict A.time)
        (fun t => P (s,t)) ∂(A.coordinateMeasure μ).fst := by
  rw [conditionalSigmaEntropy_fst (A.coordinateMeasure μ) P hP]
  apply integral_congr_ae
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree] with s hs
  rw [hs.2.2.1]
  rfl

end UpperRootBox
end DukePrimeDegree

end

end OAI
