import OAI.Analysis.CircleDomains.Uniformization.MixedLimitRealProjection
import OAI.Analysis.CircleDomains.Uniformization.SelectedRealLimit
import OAI.Analysis.CircleDomains.Selection.ProtrusionTestGeometry

namespace OAI

/-! The already constructed real barriers retain their full collapse
conclusion for the same mixed normal limit. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem AssignedMixedModelLimit.singleton_or_marked_disk_of_small_anchored
    {S C : Type*} [LinearOrder C] {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
    {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    {M : MixedModelExhaustion d data retained O ε ρ}
    (L : AssignedMixedModelLimit M)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hconn : IsConnected G) (hε : Tendsto ε atTop (𝓝 0))
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (EStar : Set Sphere)
    (houter : ∀ z ∈ sphere (0 : ℂ) (2 * M.real.radius), π (z : Sphere) ∈ EStar)
    (hsmall : ∀ b ∈ (π '' Gᶜ) \ range σ, SmallAnchoredPlateaus d EStar b)
    {p : Sphere} (hp : p ∈ (extendAtInfinity L.function '' G)ᶜ) :
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ p = {p} ∨
      ∃ s, ((↑) : ℂ → Sphere) '' closedBall (L.center s) (L.radius s) ⊆
        connectedComponentIn (extendAtInfinity L.function '' G)ᶜ p :=
  L.toReal.singleton_or_marked_disk_of_small_anchored hsard hsch harea hG hconn
    hε hπ hr EStar houter hsmall hp

end CircleDomainRigidity.FiniteTransfer

end

end OAI
