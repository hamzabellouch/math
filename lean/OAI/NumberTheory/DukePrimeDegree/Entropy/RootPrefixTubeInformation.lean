import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingLeafProduct
import OAI.NumberTheory.DukePrimeDegree.Geometry.DiagonalRootTubes

namespace OAI

/-! # Diagonal-tube information in actual conditional leaves

The local-to-ambient integral below keeps the restriction to the box
range.  In particular, it does not replace a restricted integral by a
global mean without a further argument.
-/

noncomputable section
open Matrix MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP : InitialRootPattern P} {c : EliminationChain P D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates (d+1) P T} {g : G (d+1)}

def leafBackwardTubeInformation (A : RootPrefixBox C c hP hf g)
    (R : ℝ) (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0) (ρ : ℝ) (N : ℕ)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (z : (UpperRootTransverse (d+1) × T) × c.Time) : ℝ :=
  -Real.log ((c.remainingGroupLeafMeasure hP hf (A.basedLeaf R μ z))
    (c.remainingBackwardTube ell hell ρ N)).toReal

theorem ae_leafBackwardTubeInformation_eq
    (A : RootPrefixBox C c hP hf g) (R : ℝ) (hAR : A.time ⊆ c.remainingWindow R 0)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0) (ρ : ℝ) (N : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      A.leafBackwardTubeInformation R ell hell ρ N μ z =
        c.remainingBackwardTubeInformation hP hf ell hell ρ N μ (C.timeParam c hP hf g z) := by
  filter_upwards [ae_remainingLeaf_eq_intrinsicProduct d hP c hf C g A R hAR μ] with z hz
  exact congrArg (fun ν : Measure (positiveRootGeneratedGroup (allPositiveRoots (d+1) \ P)) =>
    -Real.log (ν (c.remainingBackwardTube ell hell ρ N)).toReal) hz

theorem integrable_leafBackwardTubeInformation
    (A : RootPrefixBox C c hP hf g) (R : ℝ) (hAR : A.time ⊆ c.remainingWindow R 0)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0) (ρ : ℝ) (N : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    Integrable (A.leafBackwardTubeInformation R ell hell ρ N μ) (A.coordinateMeasure μ) := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hi := (c.integrable_remainingBackwardTubeInformation hP hf ell hell ρ N μ hA).mono_measure
    (Measure.restrict_le_self : μ.restrict A.range ≤ μ)
  rw [←A.map_coordinateMeasure μ] at hi
  apply (hi.comp_measurable (C.timeParam_localHomeomorph c hP hf g).continuous.measurable).congr
  filter_upwards [A.ae_leafBackwardTubeInformation_eq R hAR ell hell ρ N μ] with z hz
  exact hz.symm

theorem integral_leafBackwardTubeInformation
    (A : RootPrefixBox C c hP hf g) (R : ℝ) (hAR : A.time ⊆ c.remainingWindow R 0)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0) (ρ : ℝ) (N : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    (∫ z, A.leafBackwardTubeInformation R ell hell ρ N μ z ∂A.coordinateMeasure μ) =
      ∫ x in A.range, c.remainingBackwardTubeInformation hP hf ell hell ρ N μ x ∂μ := by
  rw [integral_congr_ae (A.ae_leafBackwardTubeInformation_eq R hAR ell hell ρ N μ)]
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hi := (c.integrable_remainingBackwardTubeInformation hP hf ell hell ρ N μ hA).mono_measure
    (Measure.restrict_le_self : μ.restrict A.range ≤ μ)
  rw [←A.map_coordinateMeasure μ] at hi
  have H := integral_map (C.timeParam_localHomeomorph c hP hf g).continuous.measurable.aemeasurable
    hi.aestronglyMeasurable
  rw [A.map_coordinateMeasure μ] at H
  exact H.symm

end RootPrefixBox
end DukePrimeDegree

end

end OAI
