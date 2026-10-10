import OAI.Combinatorics.ContingencyTables.Sampling.SmallContextCoordinates
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Sort

namespace OAI

/-! # Increasing enumeration of the actual finite small cells -/

namespace ContingencyTables.RowMajorEnumeration

open scoped Classical
open SmallContextCoordinates

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

abbrev LexCells (small : I → J → Bool) :=
  {a : I×ₗJ // small (ofLex a).1 (ofLex a).2=true}

noncomputable def lexCellEquiv (small : I → J → Bool) : LexCells small ≃ Cells small where
  toFun a := ⟨ofLex a.val,a.property⟩
  invFun a := ⟨toLex a.val,a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def enumeration (small : I → J → Bool) : Fin (Fintype.card (Cells small)) ≃ Cells small :=
  (monoEquivOfFin (LexCells small) (Fintype.card_congr (lexCellEquiv small))).toEquiv.trans
    (lexCellEquiv small)

lemma enumeration_before_iff (small : I → J → Bool)
    (a b : Fin (Fintype.card (Cells small))) :
    RowMajorBefore (enumeration small a).val (enumeration small b).val ↔ a<b := by
  change RowMajorBefore (ofLex ((monoEquivOfFin (LexCells small)
    (Fintype.card_congr (lexCellEquiv small))) a).val)
    (ofLex ((monoEquivOfFin (LexCells small)
    (Fintype.card_congr (lexCellEquiv small))) b).val) ↔ a<b
  have hlex : ((monoEquivOfFin (LexCells small) (Fintype.card_congr (lexCellEquiv small))) a).val <
      ((monoEquivOfFin (LexCells small) (Fintype.card_congr (lexCellEquiv small))) b).val ↔ a<b :=
    (monoEquivOfFin (LexCells small) (Fintype.card_congr (lexCellEquiv small))).lt_iff_lt
  exact (Prod.Lex.lt_iff).symm.trans hlex

noncomputable def earlierIndexEquiv (small : I → J → Bool)
    (k : Fin (Fintype.card (Cells small))) :
    Earlier small (enumeration small k).val ≃ {j : Fin (Fintype.card (Cells small)) // j<k} where
  toFun a := ⟨(enumeration small).symm a.val,by
    apply (enumeration_before_iff small _ k).mp
    simpa only [Equiv.apply_symm_apply] using a.property⟩
  invFun a := ⟨enumeration small a.val,(enumeration_before_iff small a.val k).mpr a.property⟩
  left_inv a := Subtype.ext ((enumeration small).apply_symm_apply a.val)
  right_inv a := Subtype.ext ((enumeration small).symm_apply_apply a.val)

noncomputable def laterIndexEquiv (small : I → J → Bool)
    (k : Fin (Fintype.card (Cells small))) :
    Later small (enumeration small k).val ≃ {j : Fin (Fintype.card (Cells small)) // k<j} where
  toFun a := ⟨(enumeration small).symm a.val,by
    apply (enumeration_before_iff small k _).mp
    simpa only [Equiv.apply_symm_apply] using a.property⟩
  invFun a := ⟨enumeration small a.val,(enumeration_before_iff small k a.val).mpr a.property⟩
  left_inv a := Subtype.ext ((enumeration small).apply_symm_apply a.val)
  right_inv a := Subtype.ext ((enumeration small).symm_apply_apply a.val)

def earlierFinEquiv {n : ℕ} (k : Fin n) : Fin k.val ≃ {j : Fin n // j<k} where
  toFun a := ⟨⟨a.val,by have ha := a.isLt; have hk := k.isLt; omega⟩,a.isLt⟩
  invFun a := ⟨a.val.val,a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def laterFinEquiv {n : ℕ} (k : Fin n) : Fin (n-k.val-1) ≃ {j : Fin n // k<j} where
  toFun a := ⟨⟨k.val+1+a.val,by have ha := a.isLt; have hk := k.isLt; omega⟩,by
    change k.val<k.val+1+a.val
    omega⟩
  invFun a := ⟨a.val.val-k.val-1,by have ha := a.val.isLt; have hk := a.property; omega⟩
  left_inv a := by apply Fin.ext; dsimp only; omega
  right_inv a := by apply Subtype.ext; apply Fin.ext; have ha := a.property; dsimp only; omega

noncomputable def earlierEnumeration (small : I → J → Bool)
    (k : Fin (Fintype.card (Cells small))) : Fin k.val ≃ Earlier small (enumeration small k).val :=
  (earlierFinEquiv k).trans (earlierIndexEquiv small k).symm

noncomputable def laterEnumeration (small : I → J → Bool)
    (k : Fin (Fintype.card (Cells small))) :
    Fin (Fintype.card (Cells small)-k.val-1) ≃ Later small (enumeration small k).val :=
  (laterFinEquiv k).trans (laterIndexEquiv small k).symm

omit [LinearOrder I] [LinearOrder J] in
lemma small_card_le_dimension (small : I → J → Bool) :
    Fintype.card (Cells small) ≤ Fintype.card I*Fintype.card J := by
  exact (Fintype.card_le_of_injective (fun a : Cells small => a.val) Subtype.val_injective).trans_eq
    (Fintype.card_prod I J)

end ContingencyTables.RowMajorEnumeration

end OAI
