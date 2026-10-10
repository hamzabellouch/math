import OAI.Analysis.CircleDomains.Rigidity.SelectableMaskedCoordinate
import OAI.Analysis.CircleDomains.Selection.RebasedLevelPresentations

namespace OAI

/-! Installing the preceding selected level graphs in a path code leaves
coordinates, flags, physical weights, and compatibility unchanged. -/
open Set Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace SelectableMaskedCoordinate
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}

 def withLevels (c : SelectableMaskedCoordinate d π) (H : ℕ → Set (UnitAddCircle × Sphere)) (w : ℕ → Sphere → ℝ≥0∞) :
    SelectableMaskedCoordinate { d with levels := H, levelWeights := w } π where
  coordinate := c.coordinate
  flags := c.flags
  flags_countable := c.flags_countable
  flags_dust := c.flags_dust
  weight_support := c.weight_support
  singular_marked := c.singular_marked
  domain_unique := c.domain_unique
  weighted := c.weighted

 theorem withLevels_reverse (c : SelectableMaskedCoordinate d π) (H : ℕ → Set (UnitAddCircle × Sphere)) (w : ℕ → Sphere → ℝ≥0∞) :
    (c.withLevels H w).withLevels d.levels d.levelWeights = c := by
  cases c
  rfl

 theorem CompatibleWith.withLevels {c : SelectableMaskedCoordinate d π}
    {A : Set (SelectableMaskedCoordinate d π)} (hc : c.CompatibleWith A) (H : ℕ → Set (UnitAddCircle × Sphere)) (w : ℕ → Sphere → ℝ≥0∞) :
    (c.withLevels H w).CompatibleWith ((fun a => a.withLevels H w) '' A) := by
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

 theorem withLevels_injective (H : ℕ → Set (UnitAddCircle × Sphere)) (w : ℕ → Sphere → ℝ≥0∞) :
    Injective (fun c : SelectableMaskedCoordinate d π => c.withLevels H w) := by
  intro c c' heq
  have h := congrArg (fun a => a.withLevels d.levels d.levelWeights) heq
  simpa only [withLevels_reverse] using h

end SelectableMaskedCoordinate
end CircleDomainRigidity

end

end OAI
