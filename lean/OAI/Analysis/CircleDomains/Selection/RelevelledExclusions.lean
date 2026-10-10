import OAI.Analysis.CircleDomains.Selection.CoordinateExclusionTest
import OAI.Analysis.CircleDomains.Selection.RelevelledSelection

namespace OAI

/-! Replacing the path code's level metadata changes neither a test's
physical coordinate nor its open exclusion. -/
open Set Function MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {C : MaskedCoordinateData base.physicalDomain base.quotientDomain π
    (fun x : base.dust => x.val)}

 def RealExclusionWitness.withLevels (W : RealExclusionWitness base π C) (H : ℕ → Set (UnitAddCircle × Sphere)) (w : ℕ → Sphere → ℝ≥0∞) :
    RealExclusionWitness {base with levels := H, levelWeights := w} π C where
  presentation := W.presentation.rebase (e := {base with levels := H, levelWeights := w}) rfl rfl rfl
  weight := W.weight
  weight_finite := W.weight_finite
  band_bound := W.band_bound
  radius := W.radius
  neighborhood := W.neighborhood
  isOpen_neighborhood := W.isOpen_neighborhood
  excludes := W.excludes

 def MeanExclusionTest.withLevels {hsch : PlanarSchoenflies} {p : base.dust} {B : ℝ}
    (W : MeanExclusionTest hsch base π C p B) (H : ℕ → Set (UnitAddCircle × Sphere)) (w : ℕ → Sphere → ℝ≥0∞) :
    MeanExclusionTest hsch {base with levels := H, levelWeights := w} π C p B where
  presentation := W.presentation.rebase (e := {base with levels := H, levelWeights := w}) rfl rfl rfl
  function := W.function
  continuousOn := W.continuousOn
  center := W.center
  radius := W.radius
  budgetRadius := W.budgetRadius
  witness := W.witness
  singular := W.singular
  source_bound := W.source_bound

namespace CoordinateExclusionTest
variable {hsch : PlanarSchoenflies} {B₀ : Set base.dust} {B : ℝ}

def withLevels (T : CoordinateExclusionTest hsch base π B₀ B) (H : ℕ → Set (UnitAddCircle × Sphere)) (w : ℕ → Sphere → ℝ≥0∞) :
    CoordinateExclusionTest hsch {base with levels := H, levelWeights := w} π B₀ B where
  mark := T.mark
  coordinate := T.coordinate.withLevels H w
  witness := T.witness.map (fun W => W.withLevels H w) (fun W => W.withLevels H w)

 theorem neighborhood_withLevels (T : CoordinateExclusionTest hsch base π B₀ B) (H : ℕ → Set (UnitAddCircle × Sphere)) (w : ℕ → Sphere → ℝ≥0∞) :
    (T.withLevels H w).neighborhood = T.neighborhood := by
  rcases T with ⟨p, c, W⟩
  cases W <;> rfl

 theorem withLevels_compatible {H : ℕ → Set (UnitAddCircle × Sphere)} {w : ℕ → Sphere → ℝ≥0∞}
    (T : CoordinateExclusionTest hsch {base with levels := H, levelWeights := w} π B₀ B)
    {A : Set (SelectableMaskedCoordinate base π)}
    (hT : T.coordinate.CompatibleWith ((fun c => c.withLevels H w) '' A)) :
    (T.withLevels base.levels base.levelWeights).coordinate.CompatibleWith A := by
  apply (hT.withLevels base.levels base.levelWeights).mono
  intro c hc
  exact ⟨c.withLevels H w, ⟨c, hc, rfl⟩, c.withLevels_reverse H w⟩

end CoordinateExclusionTest
end CircleDomainRigidity

end

end OAI
