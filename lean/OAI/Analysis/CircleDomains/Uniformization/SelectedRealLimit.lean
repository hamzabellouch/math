import OAI.Analysis.CircleDomains.Selection.SelectedRealCollapse
import OAI.Analysis.CircleDomains.Selection.UnmarkedRealEnds
import OAI.Analysis.CircleDomains.Transfer.EnlargedRealModels

namespace OAI

/-! The actual normal limit of the selected real models has only points
at unmarked ends. Its remaining components contain their marked round disks. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε}

theorem AssignedRealModelLimit.singleton_or_marked_disk_of_small_anchored
    (L : AssignedRealModelLimit M)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hconn : IsConnected G) (hε : Tendsto ε atTop (𝓝 0))
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (EStar : Set Sphere)
    (houter : ∀ z ∈ sphere (0 : ℂ) (2 * M.radius), π (z : Sphere) ∈ EStar)
    (hsmall : ∀ b ∈ (π '' Gᶜ) \ range σ, SmallAnchoredPlateaus d EStar b)
    {p : Sphere} (hp : p ∈ (extendAtInfinity L.function '' G)ᶜ) :
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ p = {p} ∨
      ∃ s, ((↑) : ℂ → Sphere) '' closedBall (L.center s) (L.radius s) ⊆
        connectedComponentIn (extendAtInfinity L.function '' G)ᶜ p := by
  obtain ⟨q, hq, E, hE⟩ := L.exists_source_end hG hp
  by_cases hm : π q ∈ range σ
  · obtain ⟨s, hs⟩ := hm
    exact Or.inr ⟨s, hE ▸ E.marked_disk_subset hr hq hs.symm⟩
  · left
    have hsmallq := hsmall (π q) ⟨⟨q, hq, rfl⟩, hm⟩
    have hzero : ∀ z ∈ frontier (jordanInterior (M.outerCore.disk 0)),
        π (z : Sphere) ∈ EStar := by
      rw [M.outerCore_interior,
        frontier_ball _ (ne_of_gt (mul_pos (by norm_num) M.radius_pos))]
      exact houter
    have hc := E.target_eq_singleton_of_small_anchored_coordinates hsard hsch harea
      hG hconn hε hπ hr hq M.outerCore 0 (M.component_inside_outerCore q) EStar hzero hsmallq
    simpa only [hE] using hc

end CircleDomainRigidity.FiniteTransfer

end

end OAI
