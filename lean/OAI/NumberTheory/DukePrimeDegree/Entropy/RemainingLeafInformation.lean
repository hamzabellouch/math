import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingLeafProduct
import OAI.NumberTheory.DukePrimeDegree.Entropy.RootProductInformation

namespace OAI

/-! # Information in the actual remaining-subgroup leaf is the sum of root information -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP : InitialRootPattern P} {c : EliminationChain P D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates (d+1) P T} {g : G (d+1)}

def remainingLeafInformation (A : RootPrefixBox C c hP hf g) (R : ℝ)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (t : ↥(allPositiveRoots (d+1) \ P) → ℝ)
    (z : (UpperRootTransverse (d+1) × T) × c.Time) : ℝ :=
  -Real.log ((c.remainingGroupLeafMeasure hP hf (A.basedLeaf R μ z))
    ((c.remainingGroupCoordinates hP hf).symm ''
      Set.pi univ (fun p => Metric.ball 0 (Real.exp (-t p))))).toReal

theorem ae_remainingLeafInformation_eq_sum
    (A : RootPrefixBox C c hP hf g) (R : ℝ) (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (t : ↥(allPositiveRoots (d+1) \ P) → ℝ) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      A.remainingLeafInformation R μ t z =
        ∑ p : ↥(allPositiveRoots (d+1) \ P),
          rootInformation (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2)
            μ (t p) (C.timeParam c hP hf g z) := by
  let i := fun p : ↥(allPositiveRoots (d+1) \ P) => p.val.1
  let j := fun p : ↥(allPositiveRoots (d+1) \ P) => p.val.2
  let hij := fun p : ↥(allPositiveRoots (d+1) \ P) =>
    ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2
  have hAinv (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have H := A.ae_coordinate_of_ambient μ
    (ae_rootProductInformation_eq_sum d i j hij μ hAinv t)
  filter_upwards [ae_remainingLeaf_eq_intrinsicProduct d hP c hf C g A R hAR μ,H]
    with z hz hs
  let F := (c.remainingGroupCoordinates hP hf).symm
  have hB : MeasurableSet (Set.pi univ (fun p => Metric.ball (0:ℝ) (Real.exp (-t p)))) :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => Metric.isOpen_ball.measurableSet)
  change -Real.log ((c.remainingGroupLeafMeasure hP hf (A.basedLeaf R μ z))
    (F '' Set.pi univ (fun p => Metric.ball 0 (Real.exp (-t p))))).toReal = _
  rw [hz,EliminationChain.remainingIntrinsicProduct,Measure.map_apply F.measurable
    (F.measurableEmbedding.measurableSet_image.mpr hB),F.injective.preimage_image]
  exact hs

end RootPrefixBox
end DukePrimeDegree

end

end OAI
