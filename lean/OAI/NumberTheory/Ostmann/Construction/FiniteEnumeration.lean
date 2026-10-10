import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.SDiff

namespace OAI

/-! # An explicit bridge between equivalent finite enumerations -/

namespace Ostmann

theorem finite_univ_canonical {A : Type*} [Finite A] (F : Fintype A) :
    @Finset.univ A F = @Finset.univ A (Fintype.ofFinite A) := by
  cases Subsingleton.elim F (Fintype.ofFinite A)
  rfl

theorem finset_sdiff_canonical {A : Type*} (d : DecidableEq A) (s t : Finset A) :
    @SDiff.sdiff (Finset A) (@Finset.instSDiff A d) s t =
      @SDiff.sdiff (Finset A) (@Finset.instSDiff A (Classical.decEq A)) s t := by
  cases Subsingleton.elim d (Classical.decEq A)
  rfl

end Ostmann

end OAI
