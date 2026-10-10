import OAI.Analysis.CircleDomains.Selection.ScalarTerminalRange
import OAI.Analysis.CircleDomains.Modulus.RealSourceBarriers

namespace OAI

/-! The actual matched source caps shrink to their complementary
component. Continuous component-constant tests therefore have arbitrarily
small ranges on all sufficiently late caps. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

namespace RealTargetEnd
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd L q)

 theorem eventually_source_cap_subset {V : Set Sphere} (hV : IsOpen V)
    (hsub : connectedComponentIn Gᶜ q ⊆ V) :
    ∀ᶠ n in atTop, closedTerminalCap ((L.cores n).disk (E.address n)) ⊆ V := by
  obtain ⟨N, hN⟩ := nested_sphere_sets_eventually_subset
    (fun n => (isCompact_closedTerminalCap _).isClosed) E.source_cap_antitone hV
    (by rwa [← E.source])
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (E.source_cap_antitone hn).trans hN

 theorem eventually_source_values {u : Sphere → ℝ} (hu : Continuous u)
    (hc : ∀ p ∈ connectedComponentIn Gᶜ q, u p = u q)
    {a b : ℝ} (ha : a < u q) (hb : u q < b) :
    ∀ᶠ n in atTop, ∀ p ∈ closedTerminalCap ((L.cores n).disk (E.address n)),
      u p ∈ Ioo a b := by
  apply E.eventually_source_cap_subset (isOpen_Ioo.preimage hu)
  intro p hp
  change u p ∈ Ioo a b
  rw [hc p hp]
  exact ⟨ha, hb⟩

end RealTargetEnd
end CircleDomainRigidity.FiniteTransfer

end

end OAI
