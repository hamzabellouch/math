import OAI.Analysis.CircleDomains.Selection.SelectableRealFamily
import OAI.Analysis.CircleDomains.Selection.RealSeedPresentation

namespace OAI

/-! The real seed carries the exact presentations needed by the later mixed selection. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem exists_presented_real_seed
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdense : Dense d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : d.dust = π '' d.physicalDomainᶜ) (p : d.dust) (EStar : Set Sphere)
    (hinfty : π OnePoint.infty ∈ interior EStar)
    (c : ℕ → UngatedRealTest d π EStar)
    (hc0 : (c 0).coordinate.quotient = fun _ => 0)
    (M : Set Sphere) (hM : M.Countable) (hMB : M ⊆ d.dust)
    (hcompat : OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ M)) :
    ∃ seed : ℕ → SelectableMaskedCoordinate d π,
      (∀ i, M ⊆ (seed i).flags) ∧
      (seed 0).coordinate.graph = circleBandGraph d.quotientDomain (fun _ => 0) ∧
      (∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
        (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
          (freeComponentFailure (d.dust \ ⋃ k, (seed k).flags) (seed j).coordinate.graph
            (fun k => (seed k).coordinate.graph) labels) = 0) ∧
      ∃ P : ∀ i, RealCoordinatePresentation d π (seed i).coordinate,
        ∀ i, (P i).coordinate = (c i).coordinate := by
  obtain ⟨seed, hflags, hgraph, hphysical, hbands, hzero, hcomp, ⟨hR⟩⟩ :=
    exists_selectable_real_family hcoarea d hU hG hdense π he hB p EStar c hc0 M hM hMB hcompat
  refine ⟨seed, hflags, hzero, hcomp, ?_⟩
  let P (i : ℕ) : RealCoordinatePresentation d π (seed i).coordinate :=
    (c i).levelPresentation hπ hinfty (seed i).coordinate (hgraph i) ?_
      (fun x => (hphysical i x).symm) ?_
  · refine ⟨P, fun _ => rfl⟩
  · exact hR.full_mask i
  · intro s
    rw [(hbands i s).1, (hbands i s).2]

end CircleDomainRigidity

end

end OAI
