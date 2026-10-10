import OAI.Analysis.CircleDomains.Selection.SelectedRealSmallness
import OAI.Analysis.CircleDomains.Modulus.RealAnchoredBarriers

namespace OAI

/-! Apply the selected small tests to the full target boundary component. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer.RealTargetEnd

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}

theorem target_eq_singleton_of_small_anchored_coordinates
    (E : RealTargetEnd L q)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hconn : IsConnected G) (hε : Tendsto ε atTop (𝓝 0))
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) (A : SmoothJordanCore G) (j : Fin A.count)
    (hCA : connectedComponentIn Gᶜ q ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j))
    (EStar : Set Sphere)
    (hzero : ∀ z ∈ frontier (jordanInterior (A.disk j)), π (z : Sphere) ∈ EStar)
    (hsmall : SmallAnchoredPlateaus d EStar (π q)) :
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point = {E.point} := by
  apply E.target_eq_singleton_of_small_anchored_plateaus hsard hsch harea
    hG hconn hε hπ hr hq A j hCA
  intro δ hδ
  obtain ⟨i, U, hU, hpU, hone, hz, hnorm⟩ := hsmall δ hδ
  refine ⟨i, U, hU, hpU, hone, ?_, hnorm⟩
  intro z hza
  rw [d.pullback i z (A.boundary_subset_domain j ⟨z, hza, rfl⟩)]
  exact hz _ (hzero z hza)

end CircleDomainRigidity.FiniteTransfer.RealTargetEnd

end

end OAI
