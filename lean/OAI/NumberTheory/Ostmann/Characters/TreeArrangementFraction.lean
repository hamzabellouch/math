import OAI.NumberTheory.Ostmann.Tree.ArrangementReindex
import OAI.NumberTheory.Ostmann.Tree.BadArrangementFraction
import OAI.NumberTheory.Ostmann.Characters.TreeLeafIndex

namespace OAI

/-! # Bad-arrangement fractions on the actual recursive leaf index -/

namespace Ostmann
open scoped Classical

def BadTreeArrangement {n m : ℕ} (e : Equiv.Perm (TreeLeafIndex n × Fin m)) : Prop :=
  3 * Fintype.card (TreeLeafIndex n) <
    4 * Fintype.card (arrangementGraph m e).ConnectedComponent

theorem badTreeArrangement_fraction_bound (n m : ℕ) (hm : 1 ≤ m) :
    (Fintype.card {e : Equiv.Perm (TreeLeafIndex n × Fin m) // BadTreeArrangement e} : ℝ) /
        (Fintype.card (Equiv.Perm (TreeLeafIndex n × Fin m)) : ℝ) ≤
      ((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) *
        Real.exp ((2 ^ n : ℝ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) := by
  let f : TreeLeafIndex n ≃ Fin (2 ^ n) :=
    (Fintype.equivFin _).trans (finCongr (card_treeLeafIndex n))
  let E := (f.prodCongr (Equiv.refl (Fin m))).permCongr
  have hbad (e : Equiv.Perm (TreeLeafIndex n × Fin m)) :
      BadTreeArrangement e ↔ BadBulkArrangement (E e) := by
    change _ ↔ 3 * 2 ^ n < 4 * Fintype.card (arrangementGraph m (reindexArrangement f e)).ConnectedComponent
    rw [arrangement_component_count_reindex]
    simp only [BadTreeArrangement, card_treeLeafIndex]
  have he := E.subtypeEquiv hbad
  rw [Fintype.card_congr he, Fintype.card_congr E, card_bulkPerm]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    badBulkArrangement_fraction_bound (r := 2 ^ n) (pow_pos (by decide : 0 < (2 : ℕ)) n) hm

end Ostmann

end OAI
