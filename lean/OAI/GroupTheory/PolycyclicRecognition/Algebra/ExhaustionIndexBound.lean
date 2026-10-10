import OAI.GroupTheory.PolycyclicRecognition.Analysis.BarChainExhaustion
import Mathlib.GroupTheory.Index

namespace OAI

/-! # Finite index detected by a uniformly bounded subgroup exhaustion -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem finiteIndex_of_exhaustion_index_bound (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (H : Subgroup G) (c : ℕ)
    (hfinite : ∀ n, (H.subgroupOf (S n)).FiniteIndex)
    (hbound : ∀ n, (H.subgroupOf (S n)).index ≤ c) : H.FiniteIndex := by
  classical
  rcases finite_or_infinite (G ⧸ H) with h | h
  · let := h
    exact Subgroup.finiteIndex_of_finite_quotient
  · let := h
    obtain ⟨T, hT⟩ := Finset.exists_card_eq (α := G ⧸ H) (c + 1)
    let reps : Finset G := T.image Quotient.out
    obtain ⟨n, hn⟩ := finite_subset_subgroup_exhaustion S hS hcover reps
    let a (x : T) : S n :=
      ⟨Quotient.out x.val, hn _ (Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩)⟩
    let f (x : T) : S n ⧸ H.subgroupOf (S n) := QuotientGroup.mk (a x)
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have hmem := QuotientGroup.eq.mp hxy
      have hmem' : (Quotient.out x.val)⁻¹ * Quotient.out y.val ∈ H := hmem
      have he : QuotientGroup.mk (Quotient.out x.val) =
          (QuotientGroup.mk (Quotient.out y.val) : G ⧸ H) := QuotientGroup.eq.mpr hmem'
      simpa only [Quotient.out_eq] using he
    let := hfinite n
    have hcard := Nat.card_le_card_of_injective f hf
    have htcard : T.card ≤ (H.subgroupOf (S n)).index := by
      change T.card ≤ Nat.card (S n ⧸ H.subgroupOf (S n))
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard
    have := htcard.trans (hbound n)
    omega

end PolycyclicRecognition

end

end OAI
