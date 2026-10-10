import OAI.Analysis.CircleDomains.Selection.CoordinateExclusionTest
import OAI.Analysis.CircleDomains.Selection.ReanchoredSelection

namespace OAI

/-! A local endpoint anchor changes neither an exclusion neighborhood nor
its retained coordinate. Transport back to the original selection base. -/
open Set Function MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {C : MaskedCoordinateData base.physicalDomain base.quotientDomain π
    (fun x : base.dust => x.val)}

 def RealExclusionWitness.reanchor (W : RealExclusionWitness base π C) (E : Set Sphere) :
    RealExclusionWitness {base with anchor := E} π C where
  presentation := W.presentation.rebase (e := {base with anchor := E}) rfl rfl rfl
  weight := W.weight
  weight_finite := W.weight_finite
  band_bound := W.band_bound
  radius := W.radius
  neighborhood := W.neighborhood
  isOpen_neighborhood := W.isOpen_neighborhood
  excludes := W.excludes

 def MeanExclusionTest.reanchor {hsch : PlanarSchoenflies} {p : base.dust} {B : ℝ}
    (W : MeanExclusionTest hsch base π C p B) (E : Set Sphere) :
    MeanExclusionTest hsch {base with anchor := E} π C p B where
  presentation := W.presentation.rebase (e := {base with anchor := E}) rfl rfl rfl
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

def reanchor (T : CoordinateExclusionTest hsch base π B₀ B) (E : Set Sphere) :
    CoordinateExclusionTest hsch {base with anchor := E} π B₀ B where
  mark := T.mark
  coordinate := T.coordinate.reanchor E
  witness := T.witness.map (fun W => W.reanchor E) (fun W => W.reanchor E)

 theorem neighborhood_reanchor (T : CoordinateExclusionTest hsch base π B₀ B) (E : Set Sphere) :
    (T.reanchor E).neighborhood = T.neighborhood := by
  rcases T with ⟨p, c, W⟩
  cases W <;> rfl

 theorem reanchor_compatible {E : Set Sphere}
    (T : CoordinateExclusionTest hsch {base with anchor := E} π B₀ B)
    {A : Set (SelectableMaskedCoordinate base π)}
    (hT : T.coordinate.CompatibleWith ((fun c => c.reanchor E) '' A)) :
    (T.reanchor base.anchor).coordinate.CompatibleWith A := by
  apply (hT.reanchor base.anchor).mono
  intro c hc
  exact ⟨c.reanchor E, ⟨c, hc, rfl⟩, c.reanchor_reverse E⟩

end CoordinateExclusionTest
end CircleDomainRigidity

end

end OAI
