import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarPrefixCoordinates
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace OAI

/-! # Projection of thickened endpoint tuples into increment coordinates

Bounding the auxiliary coordinates costs at most their product volume.
The subsequent change from total nilpotent coordinates to increments is
Haar preserving, including for noncommutative nilpotent groups.
-/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory
open scoped ENNReal

variable {N D : Type*} [Group N] [TopologicalSpace N] [T2Space N]
  [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N]
  [MeasurableMul₂ N] [MeasurableInv N] [TopologicalSpace D] [MeasurableSpace D]

def tupleIncrementRegion (h : ℕ) (K : Set ((Fin h → N) × D)) : Set (Fin h → N) :=
  (prefixCoordinateEquiv h).symm '' (Prod.fst '' K)

/-- The projection estimate needed before applying the polynomial endpoint
map to the joint increment set. -/
theorem tuple_lift_projection_volume (μ : Measure N) [SigmaFinite μ]
    [μ.IsMulLeftInvariant] (ν : Measure D) [SFinite ν] (h : ℕ)
    {K : Set ((Fin h → N) × D)} (hK : IsCompact K)
    {Q : Set D} (hQ : ∀ z ∈ K, z.2 ∈ Q) :
    MeasurableSet (tupleIncrementRegion h K) ∧
      ((Measure.pi fun _ : Fin h => μ).prod ν) K ≤
        (Measure.pi fun _ : Fin h => μ) (tupleIncrementRegion h K) * ν Q := by
  have hp : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hm := prefixCoordinateEquiv_symm_image_measure μ h hp.measurableSet
  refine ⟨(prefixCoordinateEquiv h).symm.measurableSet_image.mpr hp.measurableSet, ?_⟩
  rw [tupleIncrementRegion, hm]
  calc
    _ ≤ ((Measure.pi fun _ : Fin h => μ).prod ν) ((Prod.fst '' K) ×ˢ Q) := by
      apply measure_mono
      intro z hz
      exact ⟨⟨z, hz, rfl⟩, hQ z hz⟩
    _ ≤ _ := Measure.prod_prod_le _ _

end PolycyclicRecognition

end

end OAI
