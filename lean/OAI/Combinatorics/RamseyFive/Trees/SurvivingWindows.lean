import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.TreeShape

namespace OAI

namespace SharpRamseyFive.PivotTree
open TreeCodec
open scoped Classical
noncomputable section
variable {w : ℕ}

def survivingOriginal (E : Finset (Fin w)) (hE : E.Nonempty) : Fin (E.card+1)→Fin w :=
  fun i=>E.orderEmbOfFin rfl ⟨min i.val (E.card-1),by
    have h:=Finset.card_pos.mpr hE
    omega⟩

lemma survivingOriginal_mem (E : Finset (Fin w)) (hE : E.Nonempty) (i : Fin (E.card+1)) :
    survivingOriginal E hE i∈E := Finset.orderEmbOfFin_mem ..

lemma survivingOriginal_monotone (E : Finset (Fin w)) (hE : E.Nonempty) :
    Monotone (survivingOriginal E hE) := by
  intro i j hij
  apply (E.orderEmbOfFin rfl).monotone
  change min i.val (E.card-1) ≤ min j.val (E.card-1)
  exact min_le_min_right _ hij

lemma survivingOriginal_address (E : Finset (Fin w)) (hE : E.Nonempty)
    (j : Fin E.card) :
    survivingOriginal E hE (label (finiteBalanced E.card) ((finiteRankEquiv E.card).symm j))=
      E.orderEmbOfFin rfl j := by
  unfold survivingOriginal
  congr 1
  apply Fin.ext
  change min (label (finiteBalanced E.card) ((finiteRankEquiv E.card).symm j)).val (E.card-1)=j.val
  rw [finiteRankEquiv_label]
  exact min_eq_left (by omega)
end
end SharpRamseyFive.PivotTree

end OAI
