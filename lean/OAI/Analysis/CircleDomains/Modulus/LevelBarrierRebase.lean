import OAI.Analysis.CircleDomains.Modulus.BarrierRebase
import OAI.Analysis.CircleDomains.Modulus.CompatibleLevelBarrier

namespace OAI

/-! Earlier-law constraints change the base-code space, but do not change
the geometric barrier problem. Rebase its actual coordinate and size. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable [MeasurableSpace C(PathTime, Sphere)]

def CompatibleLevelBarrier.rebase {d e : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {previous : PriorLevelFamily d.physicalDomain π} {next : PriorLevelFamily e.physicalDomain π}
    {flags EStar : Set Sphere} {regions : ℕ → Set Sphere}
    {f : d.quotientDomain → Sphere} {g : e.quotientDomain → Sphere} {W : Set Sphere}
    (R : CompatibleLevelBarrier d π previous flags EStar regions f W)
    (hG : e.physicalDomain = d.physicalDomain) (hU : e.quotientDomain = d.quotientDomain)
    (hE : e.anchor = d.anchor) (hB : e.dust = d.dust)
    (hprev : ∀ i, next.graph i = previous.graph i)
    (hfg : ∀ x : e.quotientDomain, g x = f ⟨x.val, hU ▸ x.property⟩) :
    CompatibleLevelBarrier e π next flags EStar regions g W where
  coordinate := R.coordinate.rebase hG hU
  level := R.level
  penalty := R.penalty
  penalty_open := R.penalty_open
  penalty_inside := by simpa only [hU] using R.penalty_inside
  penalty_disjoint := by simpa only [hE] using R.penalty_disjoint
  penalty_avoids := by
    intro x hx
    rw [hfg x]
    exact R.penalty_avoids ⟨x.val, hU ▸ x.property⟩ hx
  zero := R.zero
  one := by simpa only [PhysicalRealCoordinate.rebase, hU] using R.one
  exclusions := R.exclusions
  exclusions_countable := R.exclusions_countable
  prior_flags := R.prior_flags
  weight := R.weight
  weight_finite := R.weight_finite
  weight_support := R.weight_support
  band_bound := by
    intro s hs
    change ENNReal.ofReal (limsup R.coordinate.quotient (𝓝[e.quotientDomain] s) -
      liminf R.coordinate.quotient (𝓝[e.quotientDomain] s)) ≤ R.weight s
    rw [hU]
    exact R.band_bound s (hB ▸ hs)
  compatible := by
    intro n labels
    simpa only [PhysicalRealCoordinate.rebase, hU, hB, hprev] using R.compatible n labels

theorem CompatibleLevelBarrier.controlledSize_rebase
    {d e : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {previous : PriorLevelFamily d.physicalDomain π} {next : PriorLevelFamily e.physicalDomain π}
    {flags EStar : Set Sphere} {regions : ℕ → Set Sphere}
    {f : d.quotientDomain → Sphere} {g : e.quotientDomain → Sphere} {W : Set Sphere}
    (R : CompatibleLevelBarrier d π previous flags EStar regions f W)
    (hG : e.physicalDomain = d.physicalDomain) (hU : e.quotientDomain = d.quotientDomain)
    (hE : e.anchor = d.anchor) (hB : e.dust = d.dust)
    (hprev : ∀ i, next.graph i = previous.graph i)
    (hfg : ∀ x : e.quotientDomain, g x = f ⟨x.val, hU ▸ x.property⟩) :
    (R.rebase hG hU hE hB hprev hfg).controlledSize = R.controlledSize := by
  simp only [CompatibleLevelBarrier.controlledSize, CompatibleLevelBarrier.rebase,
    PhysicalRealCoordinate.rebase, hG]

end CircleDomainRigidity

end

end OAI
