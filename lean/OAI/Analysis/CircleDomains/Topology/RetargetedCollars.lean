import OAI.Analysis.CircleDomains.Modulus.WeightedCollarNeighborhoods

namespace OAI

/-! Transport a constructed weighted collar along an equality of target
points without changing its physical disk or quotient region. -/
open Set
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity.WeightedCollar
variable {G B : Set Sphere} {π : Sphere → Sphere} {p q : Sphere} {g : ℂ → ℝ≥0∞}

def retarget (D : WeightedCollar G π B p g) (h : q = p) : WeightedCollar G π B q g := by
  subst q
  exact D

 theorem region_retarget (D : WeightedCollar G π B p g) (h : q = p) :
    (D.retarget h).region = D.region := by
  subst q
  rfl

end CircleDomainRigidity.WeightedCollar

end

end OAI
