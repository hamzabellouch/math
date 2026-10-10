import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

namespace OAI

namespace MatroidProphet
namespace Pivots

variable {α : Type*} [DecidableEq α]

lemma card_family_with_fixed_core (family : Finset (Finset α))
    (core extra : Finset α)
    (hcore : ∀ J ∈ family, core ⊆ J)
    (hcover : ∀ J ∈ family, J ⊆ core ∪ extra) :
    family.card ≤ 2 ^ extra.card := by
  rw [← Finset.card_powerset extra]
  apply Finset.card_le_card_of_injOn (fun J => J \ core)
  · intro J hJ
    apply Finset.mem_powerset.mpr
    intro x hx
    have hcov := hcover J hJ (Finset.mem_sdiff.mp hx).1
    exact (Finset.mem_union.mp hcov).resolve_left (Finset.mem_sdiff.mp hx).2
  · intro J hJ K hK heq
    apply Finset.ext
    intro x
    by_cases hx : x ∈ core
    · exact iff_of_true (hcore J hJ hx) (hcore K hK hx)
    · have hmem := congrArg (fun L : Finset α => x ∈ L) heq
      simpa [Finset.mem_sdiff, hx] using hmem

lemma card_retained_family (family : Finset (Finset α))
    (old movable omittable : Finset α) (s : ℕ)
    (hm : movable.card ≤ s) (ho : omittable.card ≤ s)
    (hcore : ∀ J ∈ family, old \ omittable ⊆ J)
    (hcover : ∀ J ∈ family, J ⊆ old ∪ movable) :
    family.card ≤ 4 ^ s := by
  have h := card_family_with_fixed_core family (old \ omittable)
    (omittable ∪ movable) hcore (by
      intro J hJ x hx
      rcases Finset.mem_union.mp (hcover J hJ hx) with hxold | hxmov
      · by_cases hxo : x ∈ omittable
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ hxo)
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxold, hxo⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hxmov))
  have hcard : (omittable ∪ movable).card ≤ 2 * s :=
    (Finset.card_union_le _ _).trans (by omega)
  calc
    family.card ≤ 2 ^ (omittable ∪ movable).card := h
    _ ≤ 2 ^ (2 * s) := Nat.pow_le_pow_right (by decide) hcard
    _ = 4 ^ s := by rw [pow_mul]; rfl

end Pivots
end MatroidProphet

end OAI
