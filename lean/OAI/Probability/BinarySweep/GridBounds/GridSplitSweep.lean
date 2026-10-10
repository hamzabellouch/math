import Mathlib
import OAI.Probability.BinarySweep.GridBounds.GridSplitWeights

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit

variable {X Y : Type*}
def rowPerm (f : Y → Equiv.Perm X) : Equiv.Perm (X×Y) where
  toFun xy := (f xy.2 xy.1,xy.2)
  invFun xy := ((f xy.2).symm xy.1,xy.2)
  left_inv xy := by simp
  right_inv xy := by simp

def rowPermHom : (Y → Equiv.Perm X) →* Equiv.Perm (X×Y) where
  toFun := rowPerm
  map_one' := by ext xy <;> rfl
  map_mul' f g := by ext xy <;> rfl

def columnPerm (f : X → Equiv.Perm Y) : Equiv.Perm (X×Y) where
  toFun xy := (xy.1,f xy.1 xy.2)
  invFun xy := (xy.1,(f xy.1).symm xy.2)
  left_inv xy := by simp
  right_inv xy := by simp

def columnPermHom : (X → Equiv.Perm Y) →* Equiv.Perm (X×Y) where
  toFun := columnPerm
  map_one' := by ext xy <;> rfl
  map_mul' f g := by ext xy <;> rfl

variable {m n : ℕ} (bits : Fin (m+n) → ℕ)

lemma gridLayer_left (g : GridChoices bits) (j : Fin m) (x : GridSlot bits) :
    (slotEquiv bits) (gridLayer bits g (j.castAdd n) x) =
      (gridLayer (leftBits bits) (rowChoices bits g (rightSlot bits x)) j (leftSlot bits x),
        rightSlot bits x) := by
  apply Prod.ext
  · simp only
    funext i
    change gridLayer bits g (j.castAdd n) x (i.castAdd n)=_
    by_cases hi : i=j
    · subst i
      rw [gridLayer_at,gridLayer_at,rowChoices_at]
      rfl
    · rw [gridLayer_other bits g _ _ (fun he => hi (Fin.castAdd_injective m n he)),
        gridLayer_other _ _ _ _ hi]
      rfl
  · funext i
    exact gridLayer_other bits g _ _ (by
      intro he
      have hh := congrArg (fun i : Fin (m+n) => i.val) he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega) x

lemma gridLayer_right (g : GridChoices bits) (j : Fin n) (x : GridSlot bits) :
    (slotEquiv bits) (gridLayer bits g (j.natAdd m) x) =
      (leftSlot bits x,
        gridLayer (rightBits bits) (columnChoices bits g (leftSlot bits x)) j (rightSlot bits x)) := by
  apply Prod.ext
  · funext i
    exact gridLayer_other bits g _ _ (by
      intro he
      have hh := congrArg (fun i : Fin (m+n) => i.val) he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega) x
  · simp only
    funext i
    change gridLayer bits g (j.natAdd m) x (i.natAdd m)=_
    by_cases hi : i=j
    · subst i
      rw [gridLayer_at,gridLayer_at,columnChoices_at]
      rfl
    · rw [gridLayer_other bits g _ _ (fun he => hi (Fin.natAdd_injective n m he)),
        gridLayer_other _ _ _ _ hi]
      rfl

lemma layer_left_congr (g : GridChoices bits) (j : Fin m) :
    (slotEquiv bits).permCongr (gridLayer bits g (j.castAdd n)) =
      rowPerm (fun y => gridLayer (leftBits bits) (rowChoices bits g y) j) := by
  apply Equiv.ext
  intro xy
  have he := gridLayer_left bits g j ((slotEquiv bits).symm xy)
  change (slotEquiv bits) (gridLayer bits g (j.castAdd n) ((slotEquiv bits).symm xy))= _
  rw [he]
  have ht := (slotEquiv bits).apply_symm_apply xy
  rw [show leftSlot bits ((slotEquiv bits).symm xy)=xy.1 from congrArg Prod.fst ht,
    show rightSlot bits ((slotEquiv bits).symm xy)=xy.2 from congrArg Prod.snd ht]
  rfl

lemma layer_right_congr (g : GridChoices bits) (j : Fin n) :
    (slotEquiv bits).permCongr (gridLayer bits g (j.natAdd m)) =
      columnPerm (fun x => gridLayer (rightBits bits) (columnChoices bits g x) j) := by
  apply Equiv.ext
  intro xy
  have he := gridLayer_right bits g j ((slotEquiv bits).symm xy)
  change (slotEquiv bits) (gridLayer bits g (j.natAdd m) ((slotEquiv bits).symm xy))= _
  rw [he]
  have ht := (slotEquiv bits).apply_symm_apply xy
  rw [show leftSlot bits ((slotEquiv bits).symm xy)=xy.1 from congrArg Prod.fst ht,
    show rightSlot bits ((slotEquiv bits).symm xy)=xy.2 from congrArg Prod.snd ht]
  rfl

lemma prod_rows (L : List (Y → Equiv.Perm X)) :
    (L.map rowPerm).prod=rowPerm (fun y => (L.map (fun f => f y)).prod) := by
  induction L with
  | nil => rfl
  | cons f L ih =>
    simp only [List.map_cons,List.prod_cons,ih]
    apply Equiv.ext
    intro xy
    rfl
lemma prod_columns (L : List (X → Equiv.Perm Y)) :
    (L.map columnPerm).prod=columnPerm (fun x => (L.map (fun f => f x)).prod) := by
  induction L with
  | nil => rfl
  | cons f L ih =>
    simp only [List.map_cons,List.prod_cons,ih]
    apply Equiv.ext
    intro xy
    rfl

theorem gridSweep_split (g : GridChoices bits) :
    (slotEquiv bits).permCongr (gridSweep bits g) =
      columnPerm (fun x => gridSweep (rightBits bits) (columnChoices bits g x)) *
        rowPerm (fun y => gridSweep (leftBits bits) (rowChoices bits g y)) := by
  change (slotEquiv bits).permCongrHom (gridSweep bits g)=_
  unfold gridSweep
  rw [List.ofFn_add,List.reverse_append,List.prod_append]
  rw [map_mul]
  congr 1
  · rw [map_list_prod (slotEquiv bits).permCongrHom,List.map_reverse,List.map_ofFn]
    change (List.ofFn (fun j : Fin n => (slotEquiv bits).permCongr (gridLayer bits g (j.natAdd m)))).reverse.prod=_
    simp_rw [layer_right_congr]
    simpa only [List.map_reverse,List.map_ofFn,Function.comp_def] using
      (prod_columns (List.ofFn (fun j : Fin n => fun x =>
        gridLayer (rightBits bits) (columnChoices bits g x) j)).reverse)
  · rw [map_list_prod (slotEquiv bits).permCongrHom,List.map_reverse,List.map_ofFn]
    change (List.ofFn (fun j : Fin m => (slotEquiv bits).permCongr (gridLayer bits g (j.castAdd n)))).reverse.prod=_
    simp_rw [layer_left_congr]
    simpa only [List.map_reverse,List.map_ofFn,Function.comp_def] using
      (prod_rows (List.ofFn (fun j : Fin m => fun y =>
        gridLayer (leftBits bits) (rowChoices bits g y) j)).reverse)

end BinaryCoordinateSweeps.GridSplit

end

end OAI
