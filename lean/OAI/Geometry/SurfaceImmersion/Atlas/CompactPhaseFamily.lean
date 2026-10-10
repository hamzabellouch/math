import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseCover
import OAI.Geometry.SurfaceImmersion.Geometry.SplitSupportedBounds
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseSupportCoordinates
import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateQuadraticExpansion

namespace OAI

/-! Retain the geometric charts when constructing the compact target split. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

structure CompactPhaseFamily (F : JetPolynomial.Base → JetPolynomial.Space)
    (φ : JetPolynomial.Base → ℝ) (K : Compacts SmallModes.Base) where
  centers : Finset K
  charts : centers → GoodPhaseChart (F ∘ planeCoordinateIsometry.symm) (coordinatePhase φ)
  partition : PhasePartitions.CompactPhasePartition centers K (fun i => (charts i).chart.source)

theorem exists_compactPhaseFamily
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Compacts SmallModes.Base)
    (hImm : ∀ p ∈ (K : Set SmallModes.Base),
      Function.Injective (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) p))
    (hgood : ∀ p ∈ (K : Set SmallModes.Base),
      Good (RealModes.realSecondTensor (F ∘ planeCoordinateIsometry.symm) p)
        (phaseDerivative (coordinatePhase φ) p)) : Nonempty (CompactPhaseFamily F φ K) := by
  obtain ⟨t,e,hcover⟩ := finite_good_phase_cover
    (hF.comp planeCoordinateIsometry.symm.contDiff)
    (hφ.comp planeCoordinateIsometry.symm.contDiff) K hImm hgood
  obtain ⟨P⟩ := PhasePartitions.exists_compact_phase_partition K.isCompact
    (fun i : t => (e i).chart.source) (fun i => (e i).chart.open_source) hcover
  exact ⟨⟨t,e,P⟩⟩

namespace CompactPhaseFamily
variable {F : JetPolynomial.Base → JetPolynomial.Space} {φ : JetPolynomial.Base → ℝ}
  {K : Compacts SmallModes.Base} (a : CompactPhaseFamily F φ K)

def support (i : a.centers) : Compacts JetPolynomial.Base :=
  jetSupport (a.partition.pieceSupport i)

def split (i : a.centers) : SupportedField (F := ComplexTensor) K →ₗ[ℝ]
    SupportedField (F := ComplexTensor) (modeSupport (a.support i)) :=
  (onModeSupportLM (a.partition.pieceSupport i)).comp (a.partition.splitSupportedLM i)

lemma support_subset (i : a.centers) : (modeSupport (a.support i) : Set SmallModes.Base) ⊆ K := by
  simpa only [support,modeSupport_jetSupport] using a.partition.pieceSupport_subset_original i

lemma support_chart (i : a.centers) :
    (modeSupport (a.support i) : Set SmallModes.Base) ⊆ (a.charts i).chart.source := by
  simpa only [support,modeSupport_jetSupport] using a.partition.pieceSupport_subset_domain i

lemma split_sum (f : SupportedField (F := ComplexTensor) K) (x : SmallModes.Base) :
    ∑ i, a.split i f x = f x := a.partition.sum_splitSupported_apply f x

lemma split_bound (s : ℝ≥0) (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (m : ℕ) (i : a.centers) (f : SupportedField (F := ComplexTensor) K) :
    supportedWeightedSeminorm (modeSupport (a.support i)) s m (a.split i f) ≤
      a.partition.splitConstant m * supportedWeightedSeminorm K s m f := by
  change supportedWeightedSeminorm (modeSupport (jetSupport (a.partition.pieceSupport i))) s m
    (onModeSupport (a.partition.pieceSupport i) (a.partition.splitSupported f i)) ≤ _
  rw [onModeSupport_seminorm _ s hs]
  exact a.partition.splitSupported_uniform_bound m i s hs hs1 f

end CompactPhaseFamily
end ClosedSurfaceR4.PhaseGeometry

end

end OAI
