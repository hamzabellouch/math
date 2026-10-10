import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.InitialCoverSystem

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CompiledTranslations

noncomputable def latticeWord {m : ℕ}
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    FreeGroup (SourceGeneratorLabel m) :=
  FreeGroup.map (sourceTranslationLabel m)
    (translationWordMap_surjective k).choose

theorem latticeWord_eval {m : ℕ} {H : Type*} [Group H]
    (f : SourceGeneratorLabel m → H)
    (t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →* H)
    (ht : ∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) = f (sourceTranslationLabel m i))
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    FreeGroup.lift f (latticeWord k) = t k := by
  have he : (FreeGroup.lift f).comp (FreeGroup.map (sourceTranslationLabel m)) =
      t.comp (translationWordMap (Fin m × Fin 2)) := by
    ext i
    simpa only [MonoidHom.comp_apply,FreeGroup.map.of,FreeGroup.lift_apply_of,
      translationWordMap] using (ht i).symm
  have hv := DFunLike.congr_fun he (translationWordMap_surjective k).choose
  simpa only [MonoidHom.comp_apply,latticeWord,(translationWordMap_surjective k).choose_spec] using hv

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem latticeWord_mk (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    PresentedGroup.mk (shortRelations M (alternatingGenerator a r m hm)) (latticeWord k) = B.t k := by
  have he : FreeGroup.lift (PresentedGroup.of : SourceGeneratorLabel m →
      BoundedRelationCover M (alternatingGenerator a r m hm)) =
      PresentedGroup.mk (shortRelations M (alternatingGenerator a r m hm)) := by
    ext i
    rfl
  rw [← he]
  exact latticeWord_eval _ B.t B.t_base k

end InitialCoverSystem
end CompiledTranslations

end SimpleAmenable
end
end

end OAI
