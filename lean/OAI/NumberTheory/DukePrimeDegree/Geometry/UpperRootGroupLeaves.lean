import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootGlobalCoordinates
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootLeafMeasure

namespace OAI

/-!
# Conditional measures on actual upper-unipotent group leaves

The global root-coordinate homeomorphism transports the constructed
locally finite time measures to the entire upper-unipotent group.
Their restrictions are the pushforwards of the actual box kernels.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def upperRootGroupLeafMeasure (n : ℕ) (ν : Measure (UpperRootTime n)) :
    Measure (positiveRootGeneratedGroup (allPositiveRoots n)) :=
  ν.map (upperRootWordHomeomorph n)

lemma upperRootGroupLeafMeasure_locallyFinite (n : ℕ) (ν : Measure (UpperRootTime n))
    [IsLocallyFiniteMeasure ν] : IsLocallyFiniteMeasure (upperRootGroupLeafMeasure n ν) := by
  let E := upperRootWordHomeomorph n
  constructor
  intro u
  obtain ⟨V, hu, hV, hfin⟩ := Measure.exists_isOpen_measure_lt_top ν (E.symm u)
  refine ⟨E '' V, (E.isOpenMap _ hV).mem_nhds ⟨E.symm u, hu, E.apply_symm_apply u⟩, ?_⟩
  change ν.map E (E '' V) < ⊤
  rw [Measure.map_apply E.measurable (E.isOpenMap _ hV).measurableSet,
    E.injective.preimage_image]
  exact hfin

lemma upperRootGroupLeafMeasure_apply (n : ℕ) (ν : Measure (UpperRootTime n))
    {S : Set (UpperRootTime n)} (hS : MeasurableSet S) :
    upperRootGroupLeafMeasure n ν (upperRootWordHomeomorph n '' S) = ν S := by
  rw [upperRootGroupLeafMeasure, Measure.map_apply (upperRootWordHomeomorph n).measurable
    ((upperRootWordHomeomorph n).measurableEmbedding.measurableSet_image.mpr hS),
    (upperRootWordHomeomorph n).injective.preimage_image]

lemma upperRootGroupLeafMeasure_restrict (n : ℕ) (ν : Measure (UpperRootTime n))
    {S : Set (UpperRootTime n)} (hS : MeasurableSet S) :
    (upperRootGroupLeafMeasure n ν).restrict (upperRootWordHomeomorph n '' S) =
      (ν.restrict S).map (upperRootWordHomeomorph n) := by
  rw [upperRootGroupLeafMeasure, Measure.restrict_map (upperRootWordHomeomorph n).measurable
    ((upperRootWordHomeomorph n).measurableEmbedding.measurableSet_image.mpr hS),
    (upperRootWordHomeomorph n).injective.preimage_image]

namespace UpperRootBox
variable {n : ℕ} {g : G n}

theorem ae_exists_upperRootGroupLeafMeasure (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∃ ν : Measure (positiveRootGeneratedGroup (allPositiveRoots n)),
        IsLocallyFiniteMeasure ν ∧ ν (upperRootWordHomeomorph n '' A.time) = 1 ∧
        ν.restrict (upperRootWordHomeomorph n '' A.time) =
          (A.conditionalKernel μ s).map (upperRootWordHomeomorph n) := by
  filter_upwards [A.ae_exists_upperRootLeafMeasure R hAR μ hfree] with s hs
  obtain ⟨η, hloc, hmass, hres, _⟩ := hs
  let : IsLocallyFiniteMeasure η := hloc
  refine ⟨upperRootGroupLeafMeasure n η, upperRootGroupLeafMeasure_locallyFinite n η, ?_, ?_⟩
  · rw [upperRootGroupLeafMeasure_apply n η A.time_open.measurableSet]
    exact hmass
  · rw [upperRootGroupLeafMeasure_restrict n η A.time_open.measurableSet, hres]

theorem ae_exists_upperRootGroupLeafMeasure_of_invariant
    (d : ℕ) {g : G (d + 1)} (A : UpperRootBox (d + 1) g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow (d + 1) R 0)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∃ ν : Measure (positiveRootGeneratedGroup (allPositiveRoots (d + 1))),
        IsLocallyFiniteMeasure ν ∧ ν (upperRootWordHomeomorph (d + 1) '' A.time) = 1 ∧
        ν.restrict (upperRootWordHomeomorph (d + 1) '' A.time) =
          (A.conditionalKernel μ s).map (upperRootWordHomeomorph (d + 1)) :=
  A.ae_exists_upperRootGroupLeafMeasure R hAR μ (ae_upperRoot_stabilizer_trivial d μ hA)

end UpperRootBox
end DukePrimeDegree

end

end OAI
