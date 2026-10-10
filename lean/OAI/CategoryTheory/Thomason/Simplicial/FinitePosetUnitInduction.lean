import OAI.CategoryTheory.Thomason.Strict.StrictCompositeListReplacement
import OAI.CategoryTheory.Thomason.Transfer.SimplicialRangeGluing
import Mathlib.SetTheory.Cardinal.NatCard

namespace OAI

section

/-! # Finite induction for the actual adjunction-unit comparison

Empty and greatest-element posets are the base cases. Every other finite
poset is covered by deleting two distinct maximal elements. The published
simplicial gluing lemma applies to the natural transformation on the two
actual nerve squares. All hypotheses below are proved for the constructed
Street adjunctions in the following specialization.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

/-- Two-sieve gluing for a natural comparison on ordinary poset nerves. -/
theorem comparison_two_sieve_gluing {F : SSet.{0} ⥤ SSet.{0}} (η : 𝟭 _ ⟶ F)
    (g : PublishedSimplicialGluingInput)
    {P : Type} [PartialOrder P] (A B : Set P)
    (hA : IsLowerSet A) (hB : IsLowerSet B) (hc : ∀ x, x ∈ A ∨ x ∈ B)
    (hp : IsPushout (F.map (nerveMap (interLeft A B).monotone.functor))
      (F.map (nerveMap (interRight A B).monotone.functor))
      (F.map (nerveMap (subposetInclusion A).monotone.functor))
      (F.map (nerveMap (subposetInclusion B).monotone.functor)))
    [Mono (F.map (nerveMap (subposetInclusion (A ∩ B)).monotone.functor))]
    (wA : realizationWeakEquivalences (η.app (nerve A)))
    (wB : realizationWeakEquivalences (η.app (nerve B)))
    (wI : realizationWeakEquivalences (η.app (nerve (A ∩ B : Set P)))) :
    realizationWeakEquivalences (η.app (nerve P)) := by
  have hi : nerveMap (interLeft A B).monotone.functor ≫
      nerveMap (subposetInclusion A).monotone.functor =
      nerveMap (subposetInclusion (A ∩ B)).monotone.functor :=
    (orderNerveMap_comp _ _).symm
  have : Mono (nerveMap (interLeft A B).monotone.functor) := mono_of_mono_fac hi
  have hFi : F.map (nerveMap (interLeft A B).monotone.functor) ≫
      F.map (nerveMap (subposetInclusion A).monotone.functor) =
      F.map (nerveMap (subposetInclusion (A ∩ B)).monotone.functor) := by
    rw [← F.map_comp, hi]
  have : Mono (F.map (nerveMap (interLeft A B).monotone.functor)) :=
    mono_of_mono_fac hFi
  exact g.glue (sieve_nerve_maps_isPushout A B hA hB hc) hp
    (η.app _) (η.app _) (η.app _) (η.app _)
    (η.naturality _) (η.naturality _) (η.naturality _) (η.naturality _) wI wA wB

/-- Finite induction uses the empty and greatest-element cases and the
preservation of these particular two-sieve pushouts. -/
theorem finite_poset_comparison_induction
    {F : SSet.{0} ⥤ SSet.{0}} (η : 𝟭 _ ⟶ F) (g : PublishedSimplicialGluingInput)
    (hempty : ∀ (P : Type) [PartialOrder P] [IsEmpty P],
      realizationWeakEquivalences (η.app (nerve P)))
    (hgreat : ∀ (P : Type) [PartialOrder P] (x : P), (∀ y, y ≤ x) →
      realizationWeakEquivalences (η.app (nerve P)))
    (hmono : ∀ (P : Type) [PartialOrder P] [Finite P] (A : Set P), IsLowerSet A →
      Mono (F.map (nerveMap (subposetInclusion A).monotone.functor)))
    (hpushout : ∀ (P : Type) [PartialOrder P] [Finite P] (A B : Set P),
      IsLowerSet A → IsLowerSet B → (∀ x, x ∈ A ∨ x ∈ B) →
      IsPushout (F.map (nerveMap (interLeft A B).monotone.functor))
        (F.map (nerveMap (interRight A B).monotone.functor))
        (F.map (nerveMap (subposetInclusion A).monotone.functor))
        (F.map (nerveMap (subposetInclusion B).monotone.functor)))
    (P : Type) [PartialOrder P] [Finite P] :
    realizationWeakEquivalences (η.app (nerve P)) := by
  classical
  have main : ∀ k : ℕ, ∀ (P : Type) [PartialOrder P] [Finite P], Nat.card P ≤ k →
      realizationWeakEquivalences (η.app (nerve P)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro P _ _ hcard
      cases isEmpty_or_nonempty P with
      | inl he =>
        have := he
        exact hempty P
      | inr hn =>
        have := hn
        by_cases hg : ∃ x : P, ∀ y, y ≤ x
        · obtain ⟨x, hx⟩ := hg
          exact hgreat P x hx
        obtain ⟨x, y, hx, hy, hxy⟩ := two_maximal_of_no_greatest
          (Set.toFinite (Set.univ : Set P)) Set.univ_nonempty (by
            simpa only [Set.mem_univ, true_and, forall_const] using hg)
        let A : Set P := {z | z ≠ x}
        let B : Set P := {z | z ≠ y}
        have hA : IsLowerSet A := SieveRetraction.delete_maximal_isLowerSet hx
        have hB : IsLowerSet B := SieveRetraction.delete_maximal_isLowerSet hy
        have hc : ∀ z, z ∈ A ∨ z ∈ B := by
          intro z
          by_cases hz : z = x
          · exact Or.inr (by dsimp [B]; exact fun hzy => hxy (hz.symm.trans hzy))
          · exact Or.inl hz
        have small (S : Set P) (z : P) (hz : z ∉ S) :
            realizationWeakEquivalences (η.app (nerve S)) :=
          ih (Nat.card S) ((Finite.card_subtype_lt hz).trans_le hcard) S le_rfl
        have : Mono (F.map (nerveMap (subposetInclusion (A ∩ B)).monotone.functor)) :=
          hmono P (A ∩ B) (hA.inter hB)
        exact comparison_two_sieve_gluing η g A B hA hB hc (hpushout P A B hA hB hc)
          (small A x (by simp [A])) (small B y (by simp [B]))
          (small (A ∩ B) x (by simp [A]))
  exact main (Nat.card P) P le_rfl

end Thomason.Construction

end

end OAI
