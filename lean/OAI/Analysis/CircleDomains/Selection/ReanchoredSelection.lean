import OAI.Analysis.CircleDomains.Rigidity.SelectableMaskedCoordinate
import OAI.Analysis.CircleDomains.Selection.RebasedLevelPresentations

namespace OAI

/-! A local endpoint anchor does not change a selected coordinate, its
presentation, flags, or compatibility. This permits the protrusion anchor
to be chosen after the preceding countable coordinate family. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace SelectableMaskedCoordinate
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}

 def reanchor (c : SelectableMaskedCoordinate d π) (E : Set Sphere) :
    SelectableMaskedCoordinate { d with anchor := E } π where
  coordinate := c.coordinate
  flags := c.flags
  flags_countable := c.flags_countable
  flags_dust := c.flags_dust
  weight_support := c.weight_support
  singular_marked := c.singular_marked
  domain_unique := c.domain_unique
  weighted := c.weighted

 theorem reanchor_reverse (c : SelectableMaskedCoordinate d π) (E : Set Sphere) :
    (c.reanchor E).reanchor d.anchor = c := by
  cases c
  rfl

 theorem CompatibleWith.reanchor {c : SelectableMaskedCoordinate d π}
    {A : Set (SelectableMaskedCoordinate d π)} (hc : c.CompatibleWith A) (E : Set Sphere) :
    (c.reanchor E).CompatibleWith ((fun a => a.reanchor E) '' A) := by
  constructor
  · rintro a ⟨b, hb, rfl⟩
    exact hc.1 b hb
  · intro n q hq
    choose a ha heq using hq
    have hgraphs : (fun i => (q i).coordinate.graph) =
        (fun i => (a i).coordinate.graph) := by
      funext i
      rw [← heq i]
      rfl
    change (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (d.dust \ c.flags) c.coordinate.graph
        (fun i => (q i).coordinate.graph) id) = 0
    rw [hgraphs]
    exact hc.2 n a ha

 theorem reanchor_injective (E : Set Sphere) :
    Injective (fun c : SelectableMaskedCoordinate d π => c.reanchor E) := by
  intro c c' heq
  have h := congrArg (fun a => a.reanchor d.anchor) heq
  simpa only [reanchor_reverse] using h

end SelectableMaskedCoordinate
end CircleDomainRigidity

end

end OAI
