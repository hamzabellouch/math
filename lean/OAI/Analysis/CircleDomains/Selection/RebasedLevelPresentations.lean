import OAI.Analysis.CircleDomains.Selection.SelectedLevelPresentation
import OAI.Analysis.CircleDomains.Modulus.BarrierRebase

namespace OAI

/-! Adding a target or prior law changes the code space, but preserves the
actual selected coordinates and their real/mean presentations. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

namespace FiniteTransfer.MaskedCoordinateData
variable {G U B G' U' B' : Set Sphere} {π : Sphere → Sphere}

def rebaseDust (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hG : G' = G) (hU : U' = U) (hB : B' = B) :
    MaskedCoordinateData G' U' π (fun x : B' => x.val) := by
  subst G'; subst U'; subst B'
  exact C

 theorem graph_rebaseDust (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hG : G' = G) (hU : U' = U) (hB : B' = B) :
    (C.rebaseDust hG hU hB).graph = C.graph := by
  subst G'; subst U'; subst B'
  rfl

 theorem mask_rebaseDust (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hG : G' = G) (hU : U' = U) (hB : B' = B) :
    (C.rebaseDust hG hU hB).mask = C.mask := by
  subst G'; subst U'; subst B'
  rfl

 theorem physical_rebaseDust (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hG : G' = G) (hU : U' = U) (hB : B' = B) :
    (C.rebaseDust hG hU hB).physical = C.physical := by
  subst G'; subst U'; subst B'
  rfl

 theorem singular_rebaseDust (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hG : G' = G) (hU : U' = U) (hB : B' = B) :
    ((C.rebaseDust hG hU hB).singular : Sphere) = (C.singular : Sphere) := by
  subst G'; subst U'; subst B'
  rfl

 theorem dustWeight_rebaseDust (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hG : G' = G) (hU : U' = U) (hB : B' = B) :
    (C.rebaseDust hG hU hB).dustWeight = C.dustWeight := by
  subst G'; subst U'; subst B'
  rfl

 theorem width_rebaseDust (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hG : G' = G) (hU : U' = U) (hB : B' = B) (s : B') :
    (C.rebaseDust hG hU hB).upper s - (C.rebaseDust hG hU hB).lower s =
      C.upper ⟨s.val, hB ▸ s.property⟩ - C.lower ⟨s.val, hB ▸ s.property⟩ := by
  subst G'; subst U'; subst B'
  rfl

end FiniteTransfer.MaskedCoordinateData

namespace SmoothMeanPeriodData
variable (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ))
  (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
  {G U G' U' S M : Set Sphere} {b : Sphere} {π : Sphere → Sphere}

def rebaseDomain (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (hG : G' = G) (hU : U' = U) :
    SmoothMeanPeriodData hsch K hKS η F G' U' S M b π := by
  subst G'; subst U'
  exact Q

 theorem graph_rebaseDomain (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (hG : G' = G) (hU : U' = U) :
    periodBandGraph U' M b (Q.rebaseDomain hsch K hKS η F hG hU).patch
      (Q.rebaseDomain hsch K hKS η F hG hU).branch =
      periodBandGraph U M b Q.patch Q.branch := by
  subst G'; subst U'
  rfl
end SmoothMeanPeriodData

variable [MeasurableSpace C(PathTime, Sphere)]
variable {d e : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {C : MaskedCoordinateData d.physicalDomain d.quotientDomain π (fun x : d.dust => x.val)}

 def RealCoordinatePresentation.rebase (R : RealCoordinatePresentation d π C)
    (hG : e.physicalDomain = d.physicalDomain) (hU : e.quotientDomain = d.quotientDomain)
    (hB : e.dust = d.dust) :
    RealCoordinatePresentation e π (C.rebaseDust hG hU hB) where
  coordinate := R.coordinate.rebase hG hU
  graph_eq := by
    rw [C.graph_rebaseDust]
    simpa only [PhysicalRealCoordinate.rebase, hU] using R.graph_eq
  mask_eq_univ := (C.mask_rebaseDust hG hU hB).trans R.mask_eq_univ
  physical_eq := by
    intro x
    rw [C.physical_rebaseDust]
    exact R.physical_eq x
  band_width := by
    intro s
    rw [C.width_rebaseDust]
    simpa only [PhysicalRealCoordinate.rebase, hU] using
      R.band_width ⟨s.val, hB ▸ s.property⟩
  compactSupport := R.compactSupport
  isCompact_support := R.isCompact_support
  zero_off := fun z hz hk => R.zero_off z (hG ▸ hz) hk
  zero_infty := fun hi => R.zero_infty (hG ▸ hi)

 def MeanCoordinatePresentation.rebase {hsch : PlanarSchoenflies}
    (R : MeanCoordinatePresentation hsch d π C)
    (hG : e.physicalDomain = d.physicalDomain) (hU : e.quotientDomain = d.quotientDomain)
    (hB : e.dust = d.dust) :
    MeanCoordinatePresentation hsch e π (C.rebaseDust hG hU hB) where
  arcs := R.arcs
  diskArcs := R.diskArcs
  compact_diskArcs := R.compact_diskArcs
  terminal_diskArcs := R.terminal_diskArcs
  law := R.law
  map := R.map
  arcMap := R.arcMap
  measurable_arcMap := R.measurable_arcMap
  arcMap_eq := R.arcMap_eq
  neighborhood := R.neighborhood
  mask := R.mask
  open_neighborhood := R.open_neighborhood
  closed_mask := R.closed_mask
  excludes_infty := R.excludes_infty
  boundary_domain := by simpa only [hU] using R.boundary_domain
  singular := R.singular
  singular_eq := (C.singular_rebaseDust hG hU hB).trans R.singular_eq
  singular_dust := hB.symm ▸ R.singular_dust
  singular_mask := R.singular_mask
  singular_outside := R.singular_outside
  punctured_mask := R.punctured_mask
  nonzero := R.nonzero
  unit_bound := R.unit_bound
  strict_bound := by simpa only [hU] using R.strict_bound
  injective_arcs := R.injective_arcs
  mean := R.mean.rebaseDomain hsch R.diskArcs R.terminal_diskArcs (R.law.map R.arcMap)
    R.map hG hU
  graph_eq := by
    rw [C.graph_rebaseDust, SmoothMeanPeriodData.graph_rebaseDomain]
    exact R.graph_eq

 def SelectedLevelPresentation.rebase {hsch : PlanarSchoenflies}
    (R : SelectedLevelPresentation hsch d π C)
    (hG : e.physicalDomain = d.physicalDomain) (hU : e.quotientDomain = d.quotientDomain)
    (hB : e.dust = d.dust) :
    SelectedLevelPresentation hsch e π (C.rebaseDust hG hU hB) :=
  R.map (fun Q => Q.rebase hG hU hB) (fun Q => Q.rebase hG hU hB)

end CircleDomainRigidity

end

end OAI
