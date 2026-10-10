import OAI.Analysis.CircleDomains.Selection.RealTestLevelData

namespace OAI

/-! The final marked set may contain both budget atoms and countably many
uncovered ends. The selected coordinates retain their actual boundary bands. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

def realTestCoordinateFamily
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hdense : Dense d.quotientDomain) (π : Sphere → Sphere)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : d.dust = π '' d.physicalDomainᶜ) {EStar : Set Sphere}
    (c : ℕ → UngatedRealTest d π EStar) (M : Set Sphere) (hMB : M ⊆ d.dust)
    (hM : ∀ i, (c i).exclusions ∩ d.dust ⊆ M)
    (hcompat : OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ M)) :
    FiniteTransfer.CountableRealCoordinates d.physicalDomain π (fun x : M => x.val) := by
  apply realCoordinateFamily d hU hdense π he hB (fun i => (c i).coordinate) M hMB
    (fun i => (c i).weight) (fun i => (c i).weight_finite)
    (fun i x hx hw => hM i ⟨(c i).weight_support hw, hx⟩)
    (fun i => (c i).band_bound)
  intro j n labels hlt
  have h := hcompat j n labels hlt
  have hrel : levelRelation (realTestLevelData d c).levels =
      (fun i => circleBandGraph d.quotientDomain (c i).coordinate.quotient) :=
    funext (realTestLevelData.level_relation c)
  simpa only [hrel, volume_pi] using h

theorem realTestCoordinateFamily_naturalCompatibility
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hdense : Dense d.quotientDomain) (π : Sphere → Sphere)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : d.dust = π '' d.physicalDomainᶜ) {EStar : Set Sphere}
    (c : ℕ → UngatedRealTest d π EStar) (M : Set Sphere) (hMB : M ⊆ d.dust)
    (hM : ∀ i, (c i).exclusions ∩ d.dust ⊆ M)
    (hcompat : OrderedLevelNullCompatibility (realTestLevelData d c).levels (d.dust \ M)) :
    (realTestCoordinateFamily d hU hdense π he hB c M hMB hM hcompat).NaturalCompatibility := by
  intro j n labels hlt
  have h := hcompat j n labels hlt
  have hrel : levelRelation (realTestLevelData d c).levels =
      (fun i => circleBandGraph d.quotientDomain (c i).coordinate.quotient) :=
    funext (realTestLevelData.level_relation c)
  have hm : range (fun x : M => x.val) = M := Subtype.range_coe_subtype
  change (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
    (freeComponentFailure ((π '' d.physicalDomainᶜ) \ range (fun x : M => x.val))
      (circleBandGraph d.quotientDomain (c j).coordinate.quotient)
      (fun i => circleBandGraph d.quotientDomain (c i).coordinate.quotient) labels) = 0
  simpa only [hrel, volume_pi, ← hB, hm] using h

end CircleDomainRigidity

end

end OAI
