import OAI.Combinatorics.BalancedRyser.Local.Local
import OAI.Combinatorics.BalancedRyser.Local.ReusePatternCounting

namespace OAI

namespace Balanced.Local.PatternCodes

open ReusePatternCounting
open scoped Classical
noncomputable section

variable {b κ : ℕ}

def occurrenceEquiv (b : ℕ) : Fin b × Fin 4 ≃ Fin (4 * b) :=
  (Equiv.prodComm (Fin b) (Fin 4)).trans finProdFinEquiv

def flatClasses (P : EqualityPattern b κ) (i : Fin (4 * b)) : Fin (4 * b - κ) :=
  P.classOf ((occurrenceEquiv b).symm i).1 ((occurrenceEquiv b).symm i).2

theorem flatClasses_surjective (P : EqualityPattern b κ) :
    Function.Surjective (flatClasses P) := by
  intro c
  obtain ⟨ij, hij⟩ := P.everyClass c
  refine ⟨occurrenceEquiv b ij, ?_⟩
  simpa only [flatClasses, Equiv.symm_apply_apply] using hij

def canonicalCode (P : EqualityPattern b κ) (hκ : κ ≤ 4 * b) :
    CanonicalPattern (Fin (4 * b)) κ :=
  ⟨firstRepresentative (flatClasses P), by
    refine ⟨fun i => ⟨firstRepresentative_le _ i,
      firstRepresentative_idempotent _ i⟩, ?_⟩
    rw [card_changed_firstRepresentative,
      Finset.image_univ_of_surjective (flatClasses_surjective P)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega⟩

theorem canonicalCode_equalities (P : EqualityPattern b κ) (hκ : κ ≤ 4 * b)
    (ij kl : Fin b × Fin 4) :
    (canonicalCode P hκ).1 (occurrenceEquiv b ij) =
      (canonicalCode P hκ).1 (occurrenceEquiv b kl) ↔
        P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 := by
  simpa only [canonicalCode, flatClasses, Equiv.symm_apply_apply] using
    firstRepresentative_eq_iff (flatClasses P)
      (occurrenceEquiv b ij) (occurrenceEquiv b kl)

theorem canonicalCode_eq_iff (P Q : EqualityPattern b κ) (hκ : κ ≤ 4 * b) :
    canonicalCode P hκ = canonicalCode Q hκ ↔
      ∀ (ij kl : Fin b × Fin 4),
        P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 ↔
          Q.classOf ij.1 ij.2 = Q.classOf kl.1 kl.2 := by
  constructor
  · intro h ij kl
    rw [← canonicalCode_equalities P hκ, ← canonicalCode_equalities Q hκ, h]
  · intro h
    apply Subtype.ext
    exact firstRepresentative_eq_of_same_equalities (flatClasses P) (flatClasses Q)
      (fun i j => h ((occurrenceEquiv b).symm i) ((occurrenceEquiv b).symm j))

private theorem classOf_injective : Function.Injective
    (fun P : EqualityPattern b κ => P.classOf) := by
  intro P Q h
  cases P
  cases Q
  cases h
  rfl

local instance : Fintype (EqualityPattern b κ) :=
  Fintype.ofInjective (fun P : EqualityPattern b κ => P.classOf) classOf_injective

theorem card_actual_pattern_codes_le (hb : 1 ≤ b) (hκ : κ ≤ 2) :
    (Finset.univ.image (fun P : EqualityPattern b κ =>
      canonicalCode P (by omega))).card ≤ (4 * b) ^ 4 := by
  have h := card_four_point_patterns_le b κ hb hκ
  rw [Nat.card_eq_fintype_card] at h
  exact (Finset.card_le_univ _).trans h

theorem exists_pattern_representatives (hb : 1 ≤ b) (hκ : κ ≤ 2) :
    ∃ R : Finset (EqualityPattern b κ), R.card ≤ (4 * b) ^ 4 ∧
      ∀ P : EqualityPattern b κ, ∃ Q ∈ R,
        ∀ (ij kl : Fin b × Fin 4),
          P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 ↔
            Q.classOf ij.1 ij.2 = Q.classOf kl.1 kl.2 := by
  let hk : κ ≤ 4 * b := by omega
  let S := Finset.univ.image (fun P : EqualityPattern b κ => canonicalCode P hk)
  have hex : ∀ c : S, ∃ P : EqualityPattern b κ, canonicalCode P hk = c.1 := by
    intro c
    obtain ⟨P, _, hP⟩ := Finset.mem_image.mp c.2
    exact ⟨P, hP⟩
  let rep : S → EqualityPattern b κ := fun c => Classical.choose (hex c)
  have hrep (c : S) : canonicalCode (rep c) hk = c.1 := Classical.choose_spec (hex c)
  refine ⟨Finset.univ.image rep, ?_, ?_⟩
  · calc
      (Finset.univ.image rep).card ≤ (Finset.univ : Finset S).card := Finset.card_image_le
      _ = S.card := by simp
      _ ≤ (4 * b) ^ 4 := card_actual_pattern_codes_le hb hκ
  · intro P
    let c : S := ⟨canonicalCode P hk, Finset.mem_image.mpr ⟨P, Finset.mem_univ P, rfl⟩⟩
    refine ⟨rep c, Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩, ?_⟩
    exact (canonicalCode_eq_iff P (rep c) hk).mp (hrep c).symm

def relabel (P Q : EqualityPattern b κ)
    (_h : ∀ (ij kl : Fin b × Fin 4),
      P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 ↔
        Q.classOf ij.1 ij.2 = Q.classOf kl.1 kl.2)
    (c : Fin (4 * b - κ)) : Fin (4 * b - κ) :=
  let ij := Classical.choose (P.everyClass c)
  Q.classOf ij.1 ij.2

theorem relabel_classOf (P Q : EqualityPattern b κ)
    (h : ∀ (ij kl : Fin b × Fin 4),
      P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 ↔
        Q.classOf ij.1 ij.2 = Q.classOf kl.1 kl.2)
    (ij : Fin b × Fin 4) :
    relabel P Q h (P.classOf ij.1 ij.2) = Q.classOf ij.1 ij.2 := by
  exact (h _ ij).mp (Classical.choose_spec (P.everyClass (P.classOf ij.1 ij.2)))

def classEquiv (P Q : EqualityPattern b κ)
    (h : ∀ (ij kl : Fin b × Fin 4),
      P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 ↔
        Q.classOf ij.1 ij.2 = Q.classOf kl.1 kl.2) :
    Fin (4 * b - κ) ≃ Fin (4 * b - κ) :=
  Equiv.ofBijective (relabel P Q h) (by
    constructor
    · intro c d hcd
      obtain ⟨ij, rfl⟩ := P.everyClass c
      obtain ⟨kl, rfl⟩ := P.everyClass d
      rw [relabel_classOf, relabel_classOf] at hcd
      exact (h ij kl).mpr hcd
    · intro c
      obtain ⟨ij, rfl⟩ := Q.everyClass c
      exact ⟨P.classOf ij.1 ij.2, relabel_classOf P Q h ij⟩)

theorem classEquiv_apply (P Q : EqualityPattern b κ)
    (h : ∀ (ij kl : Fin b × Fin 4),
      P.classOf ij.1 ij.2 = P.classOf kl.1 kl.2 ↔
        Q.classOf ij.1 ij.2 = Q.classOf kl.1 kl.2)
    (ij : Fin b × Fin 4) :
    classEquiv P Q h (P.classOf ij.1 ij.2) = Q.classOf ij.1 ij.2 :=
  relabel_classOf P Q h ij

end
end Balanced.Local.PatternCodes

end OAI
