import OAI.Analysis.KadisonKastler.ProductInvariantL2
import OAI.Analysis.KadisonKastler.ShiftBoundarySpace
import OAI.Analysis.KadisonKastler.ScalarInvariantProjection

namespace OAI

/-! # Descent to the first boundary coordinate

The product invariant-range theorem supplies an actual L-infinity function
on the product boundary, with unchanged norm. Thus the first-coordinate
invariant projection descends as a bounded linear map.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (S : X → X) {ν : Measure Y}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

def firstBoundaryMap (z : X × Y) : ShiftBoundarySpace μ S × Y :=
  (shiftBoundaryMap μ S z.1, z.2)

theorem firstBoundaryMap_measurePreserving :
    MeasurePreserving (firstBoundaryMap (Y := Y) μ S) (μ.prod ν)
      ((shiftBoundaryMeasure μ S).prod ν) :=
  (shiftBoundaryMap_measurePreserving μ S).prod (MeasurePreserving.id ν)

theorem firstBoundaryMeasure_eq_trim :
    (μ.prod ν).trim (firstInvariantSigma_le (Y := Y) (μ := μ) (S := S)) =
      (shiftBoundaryMeasure μ S).prod ν := by
  exact (trim_eq_map (firstInvariantSigma_le (Y := Y) (μ := μ) (S := S))).trans
    (firstBoundaryMap_measurePreserving μ S).map_eq

def firstBoundaryLiftL :
    ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν) →L[ℂ] ScalarLInfinity (μ.prod ν) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (firstBoundaryMap μ S)
    (firstBoundaryMap_measurePreserving μ S)).toContinuousLinearMap

theorem firstBoundaryLiftL_ae (g : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryLiftL μ S g =ᵐ[μ.prod ν] fun z => g (firstBoundaryMap μ S z) :=
  Lp.coeFn_compMeasurePreserving g (firstBoundaryMap_measurePreserving μ S)

theorem firstBoundaryLiftL_norm (g : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    ‖firstBoundaryLiftL μ S g‖ = ‖g‖ :=
  Lp.norm_compMeasurePreserving g (firstBoundaryMap_measurePreserving μ S)

theorem firstBoundaryLiftL_injective : Function.Injective (firstBoundaryLiftL (ν := ν) μ S) :=
  by
    intro f g h
    exact (Lp.compMeasurePreservingₗᵢ ℂ (firstBoundaryMap μ S)
      (firstBoundaryMap_measurePreserving μ S)).injective h

theorem exists_firstBoundaryLift_of_measurable (f : ScalarLInfinity (μ.prod ν))
    (hf : f ∈ lpMeas ℂ ℂ (firstInvariantSigma μ S) ⊤ (μ.prod ν)) :
    ∃ g : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν), firstBoundaryLiftL μ S g = f := by
  let g₀ := lpMeasToLpTrim ℂ ℂ ⊤ (μ.prod ν) firstInvariantSigma_le ⟨f, hf⟩
  have hg₀ : MemLp (fun z : ShiftBoundarySpace μ S × Y => g₀ z) ⊤
      ((shiftBoundaryMeasure μ S).prod ν) := by
    rw [← firstBoundaryMeasure_eq_trim μ S]
    exact Lp.memLp g₀
  let g : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν) := hg₀.toLp (fun z => g₀ z)
  refine ⟨g, Lp.ext ?_⟩
  have hg : g =ᵐ[(shiftBoundaryMeasure μ S).prod ν] fun z => g₀ z := hg₀.coeFn_toLp
  have hp : (fun z => g (firstBoundaryMap μ S z)) =ᵐ[μ.prod ν]
      (fun z => g₀ (firstBoundaryMap μ S z)) :=
    (firstBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae hg
  have h₀ : g₀ =ᵐ[μ.prod ν] f := lpMeasToLpTrim_ae_eq firstInvariantSigma_le ⟨f, hf⟩
  exact (firstBoundaryLiftL_ae μ S g).trans (hp.trans h₀)

variable {μ S}

structure FirstBoundaryProjection
    (hS : Measure.QuasiMeasurePreserving S μ μ)
    (P : ScalarInvariantProjection (firstCoordinateShift (Y := Y) S)
      (firstCoordinateShift_quasi (ν := ν) hS)) where
  toCLM : ScalarLInfinity (μ.prod ν) →L[ℂ] ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)
  lift_eq : ∀ f, firstBoundaryLiftL μ S (toCLM f) = P.toCLM f

theorem exists_firstBoundaryProjection
    (hS : Measure.QuasiMeasurePreserving S μ μ)
    (P : ScalarInvariantProjection (firstCoordinateShift (Y := Y) S)
      (firstCoordinateShift_quasi (ν := ν) hS)) : Nonempty (FirstBoundaryProjection hS P) := by
  choose E hE using fun f : ScalarLInfinity (μ.prod ν) =>
    exists_firstBoundaryLift_of_measurable μ S (P.toCLM f)
      (scalarInfinity_mem_firstInvariantSigma_of_fixed hS (P.toCLM f) (P.invariant f))
  have hn (f) : ‖E f‖ ≤ ‖f‖ := by
    rw [← firstBoundaryLiftL_norm μ S, hE]
    exact P.norm_le f
  let L : ScalarLInfinity (μ.prod ν) →ₗ[ℂ] ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν) :=
    { toFun := E
      map_add' f g := by
        apply firstBoundaryLiftL_injective μ S
        rw [map_add, hE, hE, hE, map_add]
      map_smul' c f := by
        simp only [RingHom.id_apply]
        apply firstBoundaryLiftL_injective μ S
        rw [map_smul, hE, hE, map_smul] }
  refine ⟨⟨L.mkContinuous 1 (fun f => ?_), hE⟩⟩
  change ‖E f‖ ≤ 1 * ‖f‖
  simpa using hn f

def firstBoundaryProjection
    (hS : Measure.QuasiMeasurePreserving S μ μ)
    (P : ScalarInvariantProjection (firstCoordinateShift (Y := Y) S)
      (firstCoordinateShift_quasi (ν := ν) hS)) : FirstBoundaryProjection hS P :=
  Classical.choice (exists_firstBoundaryProjection hS P)

end

end KadisonKastler

end OAI
