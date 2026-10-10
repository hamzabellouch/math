import OAI.Analysis.CircleDomains.Selection.SelectedLevelPresentation
import OAI.Analysis.CircleDomains.Modulus.RealBarrierTests
import OAI.Analysis.CircleDomains.Topology.SphereNeighborhoods

namespace OAI

/-! The real barriers used as the seed already vanish on the anchor
neighborhood of infinity. This gives the compact support required by the
later generic-level estimates, with the identical quotient coordinate. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 def UngatedRealTest.levelPresentation
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}
    (R : UngatedRealTest d π EStar)
    (hπ : Continuous π) (hinfty : π OnePoint.infty ∈ interior EStar)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (hgraph : C.graph = circleBandGraph d.quotientDomain R.coordinate.quotient)
    (hmask : C.mask = univ)
    (hphysical : ∀ x, (R.coordinate.physical x : UnitAddCircle) = C.physical x)
    (hwidth : ∀ s, C.upper s - C.lower s =
      limsup R.coordinate.quotient (𝓝[d.quotientDomain] s.val) -
        liminf R.coordinate.quotient (𝓝[d.quotientDomain] s.val)) :
    RealCoordinatePresentation d π C where
  coordinate := R.coordinate
  graph_eq := hgraph
  mask_eq_univ := hmask
  physical_eq := hphysical
  band_width := hwidth
  compactSupport := ((↑) : ℂ → Sphere) ⁻¹' (π ⁻¹' interior EStar)ᶜ
  isCompact_support := isCompact_finite_preimage
    (isOpen_interior.preimage hπ).isClosed_compl (fun h => h hinfty)
  zero_off := by
    intro z _ hz
    apply R.zero
    apply interior_subset
    by_contra hn
    exact hz hn
  zero_infty := fun _ => R.zero _ (interior_subset hinfty)

end CircleDomainRigidity

end

end OAI
