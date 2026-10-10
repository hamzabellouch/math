import OAI.Analysis.CircleDomains.Sobolev.PotentialRectangleACL
import OAI.Analysis.CircleDomains.Probability.RectangleMeasurability

namespace OAI

/-! Local area measurability of the actual bounded barrier follows from
its proved ACL property, using finite simple sampling of good slices. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Topology

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

theorem potential_rectangle_aestronglyMeasurable
    (d : PathCodeData X Sphere) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Sphere → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    {a b c e : ℝ} (hab : a < b) (hce : c < e)
    (hrect : ∀z ∈ closedComplexRectangle a b c e, (z : Sphere) ∈ d.physicalDomain) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => v ((⟨p.1, p.2⟩ : ℂ) : Sphere))
      (volume.restrict (Ioo a b ×ˢ Ioo c e)) := by
  obtain ⟨hh, hvv⟩ := potential_rectangle_ACL d hdisj ν N u g hg henergy m hm hpath v hv
    hab.le hce.le hrect
  exact aestronglyMeasurable_on_rectangle_of_ACL _ hab hce hh hvv

end CircleDomainRigidity

end OAI
