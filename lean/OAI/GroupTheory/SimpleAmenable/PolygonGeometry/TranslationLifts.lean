import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FinitelyManyTranslationRelations

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ActualTranslationLifts

def sourceTranslationLabel (m : ℕ) (i : Fin m × Fin 2) : SourceGeneratorLabel m := Sum.inr i

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)

theorem source_translation_commute (i j : Fin m × Fin 2) :
    Commute (alternatingGenerator a r m hm (Sum.inr i))
      (alternatingGenerator a r m hm (Sum.inr j)) := by
  change _ * _ = _ * _
  apply Subtype.ext
  change trackTranslation _ * trackTranslation _ = trackTranslation _ * trackTranslation _
  rw [← trackTranslation_add, ← trackTranslation_add]
  congr 1
  exact add_comm _ _

theorem source_translation_lifts_eventually :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
          BoundedRelationCover M (alternatingGenerator a r m hm),
        ∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
          PresentedGroup.of (Sum.inr i) := by
  obtain ⟨L,hL⟩ := commuting_words_lift_eventually (alternatingGenerator a r m hm)
    (fun i : Fin m × Fin 2 => FreeGroup.of (sourceTranslationLabel m i)) (by
      intro i j
      rw [FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      exact source_translation_commute a r m hm i j)
  exact ⟨L,fun M hM => let ⟨t,ht,_⟩ := hL M hM; ⟨t,ht⟩⟩

end ActualTranslationLifts

end SimpleAmenable
end
end

end OAI
