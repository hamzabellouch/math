import OAI.Geometry.SurfaceImmersion.Atlas.TensorPlaneWeight
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanData

namespace OAI

/-! The atlas cutoffs as actual compactly supported fields, and their
transport to a phase chart with the required inverse-frequency factor. -/
noncomputable section
open TopologicalSpace Set
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Manifold Bundle PhaseMean WeightedEstimates
open JetPolynomial JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def chartWeightCompact (i : A.centers) : Compacts JetPolynomial.Base :=
  ⟨(chart (i : M)) '' tsupport (A.weight i),
    (isClosed_tsupport (A.weight i)).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono (A.weight_support i))⟩

def supportedChartWeight (i : A.centers) : SupportedField (F := ℝ) (A.chartWeightCompact i) :=
  ⟨A.chartWeight i,A.chartWeight_smooth i,by
    intro x hx
    by_cases hxt : x ∈ (chart (i : M)).target
    · change (chart (i : M)).target.indicator
        (fun y => A.weight i ((chart (i : M)).symm y)) x = 0
      rw [indicator_of_mem hxt]
      by_contra hn
      exact hx ⟨(chart (i : M)).symm x,subset_tsupport (A.weight i) hn,(chart (i : M)).right_inv hxt⟩
    · exact indicator_of_notMem hxt _⟩

def supportedPlaneWeight (i : A.centers) :
    SupportedField (F := ℝ) (modeSupport (A.chartWeightCompact i)) :=
  pushSupported planeCoordinateIsometry (A.chartWeightCompact i) (A.supportedChartWeight i)

@[simp] lemma supportedPlaneWeight_apply (i : A.centers) (x : SmallModes.Base) :
    A.supportedPlaneWeight i x = A.planeWeight i x := rfl

def phaseWeightCutoff (i : A.centers)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e.symm e.target)
    (hK : (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ e.source)
    (w : ℝ) : SupportedField (F := ℝ) (chartSupport e (modeSupport (A.chartWeightCompact i)) hK) :=
  w⁻¹ • chartPush e he (modeSupport (A.chartWeightCompact i)) hK (A.supportedPlaneWeight i)

lemma phaseWeightCutoff_apply (i : A.centers)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e.symm e.target)
    (hK : (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ e.source)
    (w : ℝ) {x : SmallModes.Base} (hx : x ∈ e.source) :
    A.phaseWeightCutoff i e he hK w (e x) = A.planeWeight i x / w := by
  change w⁻¹ * chartPush e he (modeSupport (A.chartWeightCompact i)) hK
    (A.supportedPlaneWeight i) (e x) = _
  rw [chartPush_eval_source e he _ hK _ hx, A.supportedPlaneWeight_apply]
  exact (div_eq_inv_mul _ _).symm

lemma planeWeight_support_chart (i : A.centers)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (hK : (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ e.source) :
    tsupport (A.planeWeight i) ⊆ e.source := by
  have hh := (A.supportedPlaneWeight i).tsupport_subset
  have hsub : tsupport (A.planeWeight i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := hh
  exact hsub.trans hK

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
