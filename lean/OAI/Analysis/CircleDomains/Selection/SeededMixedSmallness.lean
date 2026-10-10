import OAI.Analysis.CircleDomains.Selection.SelectedMixedSmallness
import OAI.Analysis.CircleDomains.Selection.SeededLevelPresentations

namespace OAI

/-! The first selection's small real tests retain their collapse estimates through every
later mixed selection, using the original presentations at the seed labels. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem seeded_mixed_small_anchored
    {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
    {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
    {π : Sphere → Sphere}
    {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
    {hB : base.dust = π '' base.physicalDomainᶜ}
    (EStar : Set Sphere) (tests : ℕ → UngatedRealTest base π EStar)
    (seed : ℕ → SelectableMaskedCoordinate base π)
    (seedPresentation : ∀ n, RealCoordinatePresentation base π (seed n).coordinate)
    (hseed : ∀ n, (seedPresentation n).coordinate = (tests n).coordinate)
    {T : Type*} (data : T → SelectableMaskedCoordinate base π)
    (presentation : ∀ t, SelectedLevelPresentation hsch base π (data t).coordinate)
    (q : ℕ → Option T) {B₀ : Set base.dust}
    (F : SelectedMixedModels hsch base hU hdense π he hB
      (orderedSelectedCoordinates seed data q)
      (orderedSelectedPresentations seed seedPresentation data presentation q) B₀)
    (A : Set (GradedRealTest base π EStar))
    (hselected : ∀ b ∈ A, ∃ i, tests i = b.toUngatedRealTest)
    (hcover : ∀ p ∈ base.dust \ (Subtype.val '' F.marks), ∀ k,
      ∃ b ∈ A, b.grade = k ∧ p ∈ b.region)
    (p : Sphere) (hp : p ∈ base.dust \ (Subtype.val '' F.marks)) :
    SmallAnchoredPlateaus F.realCoordinates EStar p := by
  apply F.small_anchored_of_retained_tests EStar A ?_ hcover p hp
  intro b hb
  obtain ⟨i, hi⟩ := hselected b hb
  refine ⟨Sum.inlₗ i, seedPresentation i, rfl, ?_⟩
  rw [hseed, hi]

end CircleDomainRigidity

end

end OAI
