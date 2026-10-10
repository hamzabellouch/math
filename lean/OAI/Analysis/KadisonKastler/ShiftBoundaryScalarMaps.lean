import OAI.Analysis.KadisonKastler.ShiftBoundarySpace
import OAI.Analysis.KadisonKastler.ScalarInvariantProjection

namespace OAI

/-! # Scalar maps between paths and the invariant boundary

The measurable-subspace isometry implements descent and inclusion on the
actual L-infinity classes. In particular the constructed invariant
projection gives a contraction from ambient functions to boundary functions.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {S : X → X} {hS : Measure.QuasiMeasurePreserving S μ μ}

def scalarProjectionToBoundaryL (P : ScalarInvariantProjection S hS) :
    ScalarLInfinity μ →L[ℂ] ScalarLInfinity (shiftBoundaryMeasure μ S) :=
  (lpMeasToLpTrimLie ℂ ℂ ⊤ μ (shiftInvariantSigma_le μ S)).toLinearIsometry.toContinuousLinearMap.comp
    (P.toCLM.codRestrict (lpMeas ℂ ℂ (shiftInvariantSigma μ S) ⊤ μ)
      (fun f => scalarInfinity_fixed_mem_lpMeas hS (P.toCLM f) (P.invariant f)))

theorem scalarProjectionToBoundaryL_ae (P : ScalarInvariantProjection S hS)
    (f : ScalarLInfinity μ) :
    (fun x => scalarProjectionToBoundaryL P f (shiftBoundaryMap μ S x)) =ᵐ[μ] P.toCLM f :=
  lpMeasToLpTrim_ae_eq (shiftInvariantSigma_le μ S) _

theorem norm_scalarProjectionToBoundaryL (P : ScalarInvariantProjection S hS)
    (f : ScalarLInfinity μ) : ‖scalarProjectionToBoundaryL P f‖ = ‖P.toCLM f‖ :=
  lpMeasSubgroupToLpTrim_norm_map (shiftInvariantSigma_le μ S) _

theorem norm_scalarProjectionToBoundaryL_le (P : ScalarInvariantProjection S hS)
    (f : ScalarLInfinity μ) : ‖scalarProjectionToBoundaryL P f‖ ≤ ‖f‖ := by
  rw [norm_scalarProjectionToBoundaryL]
  exact P.norm_le f

def scalarBoundaryLiftL :
    ScalarLInfinity (shiftBoundaryMeasure μ S) →L[ℂ] ScalarLInfinity μ :=
  (lpMeas ℂ ℂ (shiftInvariantSigma μ S) ⊤ μ).subtypeL.comp
    (lpMeasToLpTrimLie ℂ ℂ ⊤ μ (shiftInvariantSigma_le μ S)).symm.toLinearIsometry.toContinuousLinearMap

omit [IsProbabilityMeasure μ] in
theorem scalarBoundaryLiftL_ae (f : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryLiftL f =ᵐ[μ] fun x => f (shiftBoundaryMap μ S x) :=
  lpTrimToLpMeas_ae_eq (F := ℂ) (𝕜 := ℂ) (p := ⊤) (μ := μ)
    (shiftInvariantSigma_le μ S) f

omit [IsProbabilityMeasure μ] in
theorem norm_scalarBoundaryLiftL (f : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    ‖scalarBoundaryLiftL f‖ = ‖f‖ :=
  (lpMeasToLpTrimLie ℂ ℂ ⊤ μ (shiftInvariantSigma_le μ S)).symm.norm_map f

omit [IsProbabilityMeasure μ] in
theorem scalarBoundaryLiftL_injective :
    Function.Injective (scalarBoundaryLiftL (μ := μ) (S := S)) := by
  intro f g he
  apply (lpMeasToLpTrimLie ℂ ℂ ⊤ μ (shiftInvariantSigma_le μ S)).symm.injective
  exact Subtype.ext he

omit [IsProbabilityMeasure μ] in
theorem scalarBoundaryLiftL_fixed (f : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarInfinityPullback S hS (scalarBoundaryLiftL f) = scalarBoundaryLiftL f := by
  apply scalarInfinity_fixed_of_aestronglyMeasurable
  exact mem_lpMeas_iff_aestronglyMeasurable.mp
    ((lpMeasToLpTrimLie ℂ ℂ ⊤ μ (shiftInvariantSigma_le μ S)).symm f).property

omit [IsProbabilityMeasure μ] in
theorem scalarBoundaryLiftL_positive (f : ScalarLInfinity (shiftBoundaryMeasure μ S))
    (hf : ScalarNonnegative f) : ScalarNonnegative (scalarBoundaryLiftL f) := by
  have hp := (shiftBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae hf
  filter_upwards [scalarBoundaryLiftL_ae f, hp] with x hx hp
  rwa [hx]

theorem scalarProjectionToBoundaryL_lift (P : ScalarInvariantProjection S hS)
    (f : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarProjectionToBoundaryL P (scalarBoundaryLiftL f) = f := by
  let e := lpMeasToLpTrimLie ℂ ℂ ⊤ μ (shiftInvariantSigma_le μ S)
  have hfix := P.fixed (scalarBoundaryLiftL f) (scalarBoundaryLiftL_fixed f)
  have hmem := scalarInfinity_fixed_mem_lpMeas hS (P.toCLM (scalarBoundaryLiftL f))
    (P.invariant (scalarBoundaryLiftL f))
  change e ⟨P.toCLM (scalarBoundaryLiftL f), hmem⟩ = f
  have he : (⟨P.toCLM (scalarBoundaryLiftL f), hmem⟩ :
      lpMeas ℂ ℂ (shiftInvariantSigma μ S) ⊤ μ) = e.symm f :=
    Subtype.ext hfix
  rw [he]
  exact e.apply_symm_apply f

end

end KadisonKastler

end OAI
