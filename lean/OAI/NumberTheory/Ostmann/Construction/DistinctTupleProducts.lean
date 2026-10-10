import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.Complex.Norm

namespace OAI

/-! # Grouping distinct ordered products by their underlying subsets -/

namespace Ostmann

open scoped BigOperators Classical

def tupleImage {A : Type*} [DecidableEq A] {k : ℕ} (e : Fin k ↪ A) : Finset A :=
  Finset.univ.image e

noncomputable def tupleImageFiberEquiv {A : Type*} [Fintype A] [DecidableEq A]
    (k : ℕ) (Q : Finset A) :
    {e : Fin k ↪ A // tupleImage e = Q} ≃ (Fin k ≃ Q) where
  toFun z := Equiv.ofBijective (fun i => ⟨z.1 i, by
    exact Eq.mp (congrArg (fun S : Finset A => z.1 i ∈ S) z.2)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩)
    ⟨fun i j h => z.1.injective (congrArg Subtype.val h), by
      intro a
      have ha : a.val ∈ tupleImage z.1 := by rw [z.2]; exact a.property
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
      exact ⟨i, Subtype.ext hi⟩⟩
  invFun e := ⟨e.toEmbedding.trans (Function.Embedding.subtype _), by
    ext a
    constructor
    · intro ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact (e i).property
    · intro ha
      obtain ⟨i, hi⟩ := e.surjective ⟨a, ha⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, congrArg Subtype.val hi⟩⟩
  left_inv z := by apply Subtype.ext; ext i; rfl
  right_inv e := by ext i; rfl

theorem card_tupleImage_fiber {A : Type*} [Fintype A] [DecidableEq A]
    (k : ℕ) (Q : Finset A) (hQ : Q.card = k) :
    Fintype.card {e : Fin k ↪ A // tupleImage e = Q} = k.factorial := by
  rw [Fintype.card_congr (tupleImageFiberEquiv k Q)]
  let E : Fin k ≃ Q := Fintype.equivOfCardEq (by simpa using hQ.symm)
  simpa using Fintype.card_equiv E

theorem distinct_tuple_sum {A R : Type*} [Fintype A] [DecidableEq A]
    [CommSemiring R] (k : ℕ) (y : A → R) :
    (∑ e : Fin k ↪ A, ∏ i, y (e i)) =
      (k.factorial : R) * ∑ Q ∈ (Finset.univ : Finset A).powersetCard k, ∏ a ∈ Q, y a := by
  have hmaps (e : Fin k ↪ A) (_ : e ∈ (Finset.univ : Finset (Fin k ↪ A))) :
      tupleImage e ∈ (Finset.univ : Finset A).powersetCard k := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    have hc : (Finset.univ.image e).card = (Finset.univ : Finset (Fin k)).card :=
      Finset.card_image_iff.mpr e.injective.injOn
    simpa only [tupleImage, Finset.card_univ, Fintype.card_fin] using hc
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  have hcard := (Finset.mem_powersetCard.mp hQ).2
  have hprod (e : Fin k ↪ A) (he : tupleImage e = Q) :
      (∏ i, y (e i)) = ∏ a ∈ Q, y a := by
    rw [← he, tupleImage, Finset.prod_image e.injective.injOn]
  calc
    _ = ∑ _e ∈ (Finset.univ : Finset (Fin k ↪ A)).filter (fun e => tupleImage e = Q),
        ∏ a ∈ Q, y a := by
      apply Finset.sum_congr rfl
      intro e he
      exact hprod e (Finset.mem_filter.mp he).2
    _ = _ := by
      rw [Finset.sum_const]
      have hf : ((Finset.univ : Finset (Fin k ↪ A)).filter (fun e => tupleImage e = Q)).card =
          k.factorial := by
        simpa only [Fintype.card_subtype] using card_tupleImage_fiber k Q hcard
      rw [hf]
      simp only [nsmul_eq_mul]

end Ostmann

end OAI
