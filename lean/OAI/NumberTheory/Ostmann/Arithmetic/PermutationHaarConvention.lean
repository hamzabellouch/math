import OAI.NumberTheory.Ostmann.Arithmetic.CanonicalHistoryLeafBulkHaar
import OAI.NumberTheory.Ostmann.Construction.DiagonalBadPairInversionComponents

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.PermutationHaarConvention
open Conclusion

def rowConjugate {r m : ℕ} (e : Equiv.Perm (Fin r))
    (σ : Equiv.Perm (Fin r × Fin m)) : Equiv.Perm (Fin r × Fin m) :=
  (e.prodCongr (Equiv.refl (Fin m))).trans
    (σ.trans (e.prodCongr (Equiv.refl (Fin m))).symm)

theorem overlapRelation_rowConjugate {r m : ℕ} (e : Equiv.Perm (Fin r))
    (σ : Equiv.Perm (Fin r × Fin m)) (a b : Fin r) :
    overlapRelation (rowConjugate e σ) a b ↔ overlapRelation σ (e a) (e b) := by
  change (∃ u v : Fin m, e.symm (σ (e a,u)).1 = e.symm (σ (e b,v)).1) ↔ _
  exact exists_congr fun u => exists_congr fun v => e.symm.injective.eq_iff

private theorem eqvGen_map {A B : Type*} {R : A → A → Prop} {S : B → B → Prop}
    (f : A → B) (hf : ∀ a b, R a b → S (f a) (f b))
    {a b : A} (h : Relation.EqvGen R a b) : Relation.EqvGen S (f a) (f b) := by
  induction h with
  | rel a b h => exact .rel _ _ (hf a b h)
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c h₁ h₂ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem overlapClosure_rowConjugate {r m : ℕ} (e : Equiv.Perm (Fin r))
    (σ : Equiv.Perm (Fin r × Fin m)) (a b : Fin r) :
    Relation.EqvGen (overlapRelation (rowConjugate e σ)) a b ↔
      Relation.EqvGen (overlapRelation σ) (e a) (e b) := by
  constructor
  · exact eqvGen_map e (fun u v => (overlapRelation_rowConjugate e σ u v).mp)
  · intro h
    have hh := eqvGen_map e.symm (fun u v huv =>
      (overlapRelation_rowConjugate e σ (e.symm u) (e.symm v)).mpr
        (by simpa only [Equiv.apply_symm_apply] using huv)) h
    simpa only [Equiv.symm_apply_apply] using hh

def rowComponentEquiv {r m : ℕ} (e : Equiv.Perm (Fin r))
    (σ : Equiv.Perm (Fin r × Fin m)) :
    OverlapComponent (rowConjugate e σ) ≃ OverlapComponent σ :=
  Quotient.congr e (overlapClosure_rowConjugate e σ)

theorem overlapComponent_card_rowConjugate {r m : ℕ} (e : Equiv.Perm (Fin r))
    (σ : Equiv.Perm (Fin r × Fin m)) :
    Fintype.card (OverlapComponent (rowConjugate e σ)) =
      Fintype.card (OverlapComponent σ) := Fintype.card_congr (rowComponentEquiv e σ)

theorem haarPermutation_blocks {l m : ℕ} (σ : Equiv.Perm (Fin (2^l) × Fin m)) :
    TreePermutationHaar.blocks (CanonicalHistoryLeafBulk.haarPermutation σ) =
      TreePermutationHaar.blocks σ := by
  change Fintype.card (OverlapComponent
    (rowConjugate (CanonicalHistoryLeafBulk.addressChange l) σ.symm)) = _
  rw [overlapComponent_card_rowConjugate,overlapComponent_card_symm]

@[simp] theorem haarPermutation_badArrangement_iff {l m : ℕ}
    (σ : Equiv.Perm (Fin (2^l) × Fin m)) :
    BadArrangement (CanonicalHistoryLeafBulk.haarPermutation σ) ↔ BadArrangement σ := by
  unfold BadArrangement
  rw [show Fintype.card (OverlapComponent (CanonicalHistoryLeafBulk.haarPermutation σ)) =
    Fintype.card (OverlapComponent σ) from haarPermutation_blocks σ]

@[simp] theorem haarPermutation_transferBadArrangement_iff {l m : ℕ}
    (σ : Equiv.Perm (Fin (2^l) × Fin m)) :
    TransferBadArrangement (CanonicalHistoryLeafBulk.haarPermutation σ) ↔ TransferBadArrangement σ := by
  simp only [TransferBadArrangement,haarPermutation_badArrangement_iff]

theorem haarPermutation_good {l m : ℕ} (σ : Equiv.Perm (Fin (2^l) × Fin m))
    (h : ¬ TransferBadArrangement σ) :
    ¬ TransferBadArrangement (CanonicalHistoryLeafBulk.haarPermutation σ) :=
  h ∘ (haarPermutation_transferBadArrangement_iff σ).mp

end Ostmann.Arithmetic.PermutationHaarConvention

end

end OAI
