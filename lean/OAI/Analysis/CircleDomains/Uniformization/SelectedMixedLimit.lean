import OAI.Analysis.CircleDomains.Selection.SelectedMixedSmallness
import OAI.Analysis.CircleDomains.Selection.MixedRealCollapse

namespace OAI

/-! Construct a normal limit of the selected mixed family and apply the retained real
barriers to that same limit. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

namespace SelectedMixedModels
variable {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere}
  {hU : IsOpen base.quotientDomain} {hdense : Dense base.quotientDomain}
  {π : Sphere → Sphere}
  {he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val}
  {hB : base.dust = π '' base.physicalDomainᶜ}
  {I : Type*} [LinearOrder I] {D : I → SelectableMaskedCoordinate base π}
  {presentation : ∀ l, SelectedLevelPresentation hsch base π (D l).coordinate}
  {B₀ : Set base.dust}

 theorem exists_normal_limit_with_real_collapse
    (F : SelectedMixedModels hsch base hU hdense π he hB D presentation B₀)
    (hsard : SmoothPlanarSard) (harea : ExteriorCoefficientAreaTheorem) (hmontel : MontelExhaustion)
    (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (hG : IsOpen base.physicalDomain) (hconn : IsConnected base.physicalDomain)
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (EStar : Set Sphere)
    (houter : ∀ z ∈ sphere (0 : ℂ) (2 * F.model.real.radius), π (z : Sphere) ∈ EStar)
    (hsmall : ∀ p ∈ base.dust \ (Subtype.val '' F.marks),
      SmallAnchoredPlateaus F.realCoordinates EStar p) :
    ∃ A : AssignedMixedModelLimit F.model,
      ∀ p ∈ (extendAtInfinity A.function '' base.physicalDomain)ᶜ,
        connectedComponentIn (extendAtInfinity A.function '' base.physicalDomain)ᶜ p = {p} ∨
        ∃ s : F.marks, ((↑) : ℂ → Sphere) '' closedBall (A.center s) (A.radius s) ⊆
          connectedComponentIn (extendAtInfinity A.function '' base.physicalDomain)ᶜ p := by
  let : Countable F.marks := F.marks_countable.to_subtype
  obtain ⟨A⟩ := F.model.exists_assigned_limit harea hmontel hhurwitz hzero hsard hsch hG hconn
  refine ⟨A, ?_⟩
  intro p hp
  apply A.singleton_or_marked_disk_of_small_anchored hsard hsch harea hG hconn
    modelError_tendsto hπ hr EStar houter ?_ hp
  intro b hb
  apply hsmall b
  constructor
  · exact hB.symm ▸ hb.1
  · intro hm
    obtain ⟨s, hs, hsb⟩ := hm
    exact hb.2 ⟨⟨s, hs⟩, hsb⟩

end SelectedMixedModels
end CircleDomainRigidity

end

end OAI
