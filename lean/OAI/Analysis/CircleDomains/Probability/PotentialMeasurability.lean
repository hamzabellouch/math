import OAI.Analysis.CircleDomains.Probability.PotentialRectangleMeasurability
import OAI.Analysis.CircleDomains.Topology.RectangleNeighborhoods
import OAI.Analysis.CircleDomains.Sobolev.SmoothRealSphereMaps

namespace OAI

/-! The actual barrier is area measurable throughout the physical domain,
by a countable patching of the proved rectangle ACL representatives. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Topology

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

theorem potential_physical_aestronglyMeasurable
    (d : PathCodeData X Sphere) (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Sphere → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => v ((⟨p.1, p.2⟩ : ℂ) : Sphere))
      (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain)) := by
  apply aestronglyMeasurable_on_open_of_rectangles (isOpen_realChartDomain hG)
  intro a b c e hab hce hrect
  apply potential_rectangle_aestronglyMeasurable d hdisj ν N u g hg henergy m hm hpath v hv hab hce
  rintro z ⟨p, hp, rfl⟩
  exact hrect hp

end CircleDomainRigidity

end OAI
