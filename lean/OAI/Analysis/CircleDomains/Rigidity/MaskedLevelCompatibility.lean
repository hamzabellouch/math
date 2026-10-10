import OAI.Analysis.CircleDomains.Selection.PeriodBandGraph
import OAI.Analysis.CircleDomains.Modulus.LevelIncidence

namespace OAI

/-! Restricting the free set to a mask neighborhood loses no compatibility
conditions: the new period levels have no incidences outside their mask,
and their distinguished point has already been flagged. -/

open Set Function

namespace CircleDomainRigidity

theorem freeComponentFailure_inter_eq_of_support
    {X T J Λ : Type*} [TopologicalSpace X]
    (Free S : Set X) (Rnew : Set (X × T)) (R : Λ → Set (X × T)) (labels : J → Λ)
    (hs : ∀ x ∈ Free, ∀ t, (x, t) ∈ Rnew → x ∈ S) :
    freeComponentFailure (Free ∩ S) Rnew R labels =
      freeComponentFailure Free Rnew R labels := by
  apply Subset.antisymm
  · rintro p ⟨⟨x, q⟩, h, rfl⟩
    exact ⟨(x, q), ⟨h.1.1, h.2⟩, rfl⟩
  · rintro p ⟨⟨x, q⟩, h, rfl⟩
    exact ⟨(x, q), ⟨⟨h.1, hs x h.1 q.1 h.2.1⟩, h.2⟩, rfl⟩

theorem freeComponentFailure_periodBandGraph_eq
    {I J Λ : Type*} (D M Free S : Set Sphere) (b : Sphere) (hb : b ∉ Free)
    (hMS : M \ {b} ⊆ S) (V : I → Set Sphere) (f : I → Sphere → ℝ)
    (R : Λ → Set (Sphere × UnitAddCircle)) (labels : J → Λ) :
    freeComponentFailure (Free ∩ S) (periodBandGraph D M b V f) R labels =
      freeComponentFailure Free (periodBandGraph D M b V f) R labels := by
  apply freeComponentFailure_inter_eq_of_support
  intro x hx θ hθ
  exact hMS ⟨hθ.1, fun he => hb (he ▸ hx)⟩

end CircleDomainRigidity

end OAI
