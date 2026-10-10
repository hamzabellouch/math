import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite

namespace OAI

/-! # A finite tuple criterion for bounded subgroup index -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

def CosetCollisionBound (H : Subgroup G) (b : ℕ) : Prop :=
  ∀ f : Fin (b + 1) → G, ∃ i j, i ≠ j ∧ (f i)⁻¹ * f j ∈ H

theorem finiteIndex_of_cosetCollisionBound (H : Subgroup G) (b : ℕ)
    (h : CosetCollisionBound H b) : H.FiniteIndex ∧ H.index ≤ b := by
  classical
  have hn : ¬ Nonempty (Fin (b + 1) ↪ (G ⧸ H)) := by
    rintro ⟨e⟩
    obtain ⟨i, j, hij, hm⟩ := h (fun i => Quotient.out (e i))
    apply hij
    apply e.injective
    have he : (Quotient.mk'' (Quotient.out (e i)) : G ⧸ H) =
        Quotient.mk'' (Quotient.out (e j)) :=
      Quotient.sound (QuotientGroup.leftRel_apply.mpr hm)
    simpa only [Quotient.out_eq'] using he
  have hfin : Finite (G ⧸ H) := by
    by_contra hf
    let : Infinite (G ⧸ H) := not_finite_iff_infinite.mp hf
    apply hn
    exact ⟨⟨fun i => Infinite.natEmbedding (G ⧸ H) i.val,
      (Infinite.natEmbedding (G ⧸ H)).injective.comp Fin.val_injective⟩⟩
  let := hfin
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  refine ⟨Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  by_contra hb
  apply hn
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_fin, ← Nat.card_eq_fintype_card, H.index_eq_card, Nat.card_fin] using
    Nat.succ_le_of_lt (lt_of_not_ge hb)

theorem cosetCollisionBound_of_index (H : Subgroup G) [H.FiniteIndex]
    (b : ℕ) (hb : H.index ≤ b) : CosetCollisionBound H b := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  intro f
  by_contra h
  have hf : Function.Injective (fun i => (Quotient.mk'' (f i) : G ⧸ H)) := by
    intro i j hij
    by_contra hne
    exact h ⟨i, j, hne, QuotientGroup.leftRel_apply.mp (Quotient.exact hij)⟩
  have hc := Fintype.card_le_of_injective _ hf
  have hb' : Fintype.card (G ⧸ H) ≤ b := by
    simpa only [← Nat.card_eq_fintype_card, ← H.index_eq_card] using hb
  simp only [Fintype.card_fin] at hc
  change b + 1 ≤ Fintype.card (G ⧸ H) at hc
  omega

end PolycyclicRecognition

end

end OAI
