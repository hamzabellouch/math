import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.SignedBlock
import OAI.Probability.BinarySweep.GridBounds.GridSplitSweep
import OAI.Probability.BinarySweep.FiniteLaws.OneCard

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.BinarySplit
variable {m n : ℕ}

def fillSlot {d : ℕ} (j : Fin d) (u : {i : Fin d // i≠j} → Bool) : Slot d :=
  (Equiv.piSplitAt j (fun _ => Bool)).symm (false,u)

lemma fillSlot_other {d : ℕ} (j : Fin d) (u : {i : Fin d // i≠j} → Bool)
    (i : Fin d) (hi : i≠j) : fillSlot j u i=u ⟨i,hi⟩ := by
  simp [fillSlot,Equiv.piSplitAt,hi]

def leftOutsideEquiv (j : Fin m) :
    ({i : Fin (m+n) // i≠j.castAdd n} → Bool) ≃ Slot n × ({i : Fin m // i≠j} → Bool) where
  toFun u := (fun i => u ⟨i.natAdd m,by intro h; have hh := congrArg (fun q:Fin (m+n) => q.val) h; simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega⟩,
    fun i => u ⟨i.val.castAdd n,fun h => i.property (Fin.ext (congrArg (fun q:Fin (m+n) => q.val) h))⟩)
  invFun yu i := Fin.addCases (fillSlot j yu.2) yu.1 i.val
  left_inv u := by
    funext i
    rcases i with ⟨i,hi⟩
    revert hi
    induction i using Fin.addCases with
    | left i =>
      intro hi
      have hij : i≠j := fun h => hi (congrArg (Fin.castAdd n) h)
      simp only [Fin.addCases_left,fillSlot_other _ _ _ hij]
    | right i => intro hi; simp only [Fin.addCases_right]
  right_inv yu := by
    apply Prod.ext
    · funext i
      simp only [Fin.addCases_right]
    · funext i
      simp only [Fin.addCases_left,fillSlot_other _ _ _ i.property]

def rightOutsideEquiv (j : Fin n) :
    ({i : Fin (m+n) // i≠j.natAdd m} → Bool) ≃ Slot m × ({i : Fin n // i≠j} → Bool) where
  toFun u := (fun i => u ⟨i.castAdd n,by intro h; have hh := congrArg (fun q:Fin (m+n) => q.val) h; simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega⟩,
    fun i => u ⟨i.val.natAdd m,fun h => i.property (Fin.ext (by have hh := congrArg (fun q:Fin (m+n) => q.val) h; simpa using hh))⟩)
  invFun xu i := Fin.addCases xu.1 (fillSlot j xu.2) i.val
  left_inv u := by
    funext i
    rcases i with ⟨i,hi⟩
    revert hi
    induction i using Fin.addCases with
    | left i => intro hi; simp only [Fin.addCases_left]
    | right i =>
      intro hi
      have hij : i≠j := fun h => hi (congrArg (Fin.natAdd m) h)
      simp only [Fin.addCases_right,fillSlot_other _ _ _ hij]
  right_inv xu := by
    apply Prod.ext
    · funext i
      simp only [Fin.addCases_left]
    · funext i
      simp only [Fin.addCases_right,fillSlot_other _ _ _ i.property]

def rowChoices (g : SweepCoins (m+n)) (y : Slot n) : SweepCoins m :=
  fun j u => g (j.castAdd n) ((leftOutsideEquiv j).symm (y,u))
def columnChoices (g : SweepCoins (m+n)) (x : Slot m) : SweepCoins n :=
  fun j u => g (j.natAdd m) ((rightOutsideEquiv j).symm (x,u))

def joinChoices (L : Slot n → SweepCoins m)
    (R : Slot m → SweepCoins n) : SweepCoins (m+n) :=
  Fin.addCases (fun j u => L ((leftOutsideEquiv j) u).1 j ((leftOutsideEquiv j) u).2)
    (fun j u => R ((rightOutsideEquiv j) u).1 j ((rightOutsideEquiv j) u).2)

def choicesEquiv : SweepCoins (m+n) ≃
    (Slot n → SweepCoins m) ×
    (Slot m → SweepCoins n) where
  toFun g := (rowChoices g,columnChoices g)
  invFun LR := joinChoices LR.1 LR.2
  left_inv g := by
    funext j u
    induction j using Fin.addCases with
    | left j => simp [joinChoices,rowChoices]
    | right j => simp [joinChoices,columnChoices]
  right_inv LR := by
    apply Prod.ext
    · funext y j u
      simp [rowChoices,joinChoices]
    · funext x j u
      simp [columnChoices,joinChoices]

end BinaryCoordinateSweeps.BinarySplit

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.BinarySplit
open GridSplit

variable {m n : ℕ}

lemma rowChoices_at (c : SweepCoins (m+n)) (x : Slot (m+n)) (j : Fin m) :
    rowChoices c (Signed.splitWord x).2 j (fun i => (Signed.splitWord x).1 i)=
      c (j.castAdd n) (fun i => x i) := by
  unfold rowChoices
  congr 1
  apply (leftOutsideEquiv j).injective
  rw [Equiv.apply_symm_apply]
  rfl

lemma columnChoices_at (c : SweepCoins (m+n)) (x : Slot (m+n)) (j : Fin n) :
    columnChoices c (Signed.splitWord x).1 j (fun i => (Signed.splitWord x).2 i)=
      c (j.natAdd m) (fun i => x i) := by
  unfold columnChoices
  congr 1
  apply (rightOutsideEquiv j).injective
  rw [Equiv.apply_symm_apply]
  rfl

lemma layer_left (c : SweepCoins (m+n)) (j : Fin m) (x : Slot (m+n)) :
    Signed.splitWord (coordinateLayer (m+n) (j.castAdd n) (c (j.castAdd n)) x)=
      (coordinateLayer m j (rowChoices c (Signed.splitWord x).2 j) (Signed.splitWord x).1,
        (Signed.splitWord x).2) := by
  apply Prod.ext
  · dsimp only
    funext i
    change coordinateLayer _ _ _ x (i.castAdd n)=_
    by_cases hi : i=j
    · subst i
      rw [coordinateLayer_apply_at,coordinateLayer_apply_at,rowChoices_at]
      rfl
    · rw [coordinateLayer_apply_other _ _ _ (fun he => hi (Fin.ext
        (congrArg (fun i : Fin (m+n) => i.val) he))),coordinateLayer_apply_other _ _ _ hi]
      rfl
  · dsimp only
    funext i
    exact coordinateLayer_apply_other (m+n) (j.castAdd n) (i.natAdd m) (by
      intro he
      have hh := congrArg (fun i : Fin (m+n) => i.val) he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega) _ x

lemma layer_right (c : SweepCoins (m+n)) (j : Fin n) (x : Slot (m+n)) :
    Signed.splitWord (coordinateLayer (m+n) (j.natAdd m) (c (j.natAdd m)) x)=
      ((Signed.splitWord x).1,
        coordinateLayer n j (columnChoices c (Signed.splitWord x).1 j) (Signed.splitWord x).2) := by
  apply Prod.ext
  · dsimp only
    funext i
    exact coordinateLayer_apply_other (m+n) (j.natAdd m) (i.castAdd n) (by
      intro he
      have hh := congrArg (fun i : Fin (m+n) => i.val) he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega) _ x
  · dsimp only
    funext i
    change coordinateLayer _ _ _ x (i.natAdd m)=_
    by_cases hi : i=j
    · subst i
      rw [coordinateLayer_apply_at,coordinateLayer_apply_at,columnChoices_at]
      rfl
    · rw [coordinateLayer_apply_other _ _ _ (fun he => hi (Fin.ext (by
        have hh := congrArg (fun i : Fin (m+n) => i.val) he; simpa using hh))),
        coordinateLayer_apply_other _ _ _ hi]
      rfl

lemma layer_left_congr (c : SweepCoins (m+n)) (j : Fin m) :
    Signed.splitWord.permCongr (coordinateLayer (m+n) (j.castAdd n) (c (j.castAdd n)))=
      rowPerm (fun y => coordinateLayer m j (rowChoices c y j)) := by
  apply Equiv.ext
  intro xy
  have he := layer_left c j (Signed.splitWord.symm xy)
  change Signed.splitWord (coordinateLayer _ _ _ (Signed.splitWord.symm xy))=_
  rw [he,Equiv.apply_symm_apply]
  rfl

lemma layer_right_congr (c : SweepCoins (m+n)) (j : Fin n) :
    Signed.splitWord.permCongr (coordinateLayer (m+n) (j.natAdd m) (c (j.natAdd m)))=
      columnPerm (fun x => coordinateLayer n j (columnChoices c x j)) := by
  apply Equiv.ext
  intro xy
  have he := layer_right c j (Signed.splitWord.symm xy)
  change Signed.splitWord (coordinateLayer _ _ _ (Signed.splitWord.symm xy))=_
  rw [he,Equiv.apply_symm_apply]
  rfl

theorem binarySweep_split (c : SweepCoins (m+n)) :
    Signed.splitWord.permCongr (binarySweep (m+n) c)=
      columnPerm (fun x => binarySweep n (columnChoices c x)) *
        rowPerm (fun y => binarySweep m (rowChoices c y)) := by
  change Signed.splitWord.permCongrHom (binarySweep (m+n) c)=_
  unfold binarySweep
  rw [List.ofFn_add,List.reverse_append,List.prod_append,map_mul]
  congr 1
  · rw [map_list_prod Signed.splitWord.permCongrHom,List.map_reverse,List.map_ofFn]
    change (List.ofFn (fun j : Fin n => Signed.splitWord.permCongr
      (coordinateLayer _ (j.natAdd m) (c (j.natAdd m))))).reverse.prod=_
    simp_rw [layer_right_congr]
    simpa only [List.map_reverse,List.map_ofFn,Function.comp_def] using
      (prod_columns (List.ofFn (fun j : Fin n => fun x =>
        coordinateLayer n j (columnChoices c x j))).reverse)
  · rw [map_list_prod Signed.splitWord.permCongrHom,List.map_reverse,List.map_ofFn]
    change (List.ofFn (fun j : Fin m => Signed.splitWord.permCongr
      (coordinateLayer _ (j.castAdd n) (c (j.castAdd n))))).reverse.prod=_
    simp_rw [layer_left_congr]
    simpa only [List.map_reverse,List.map_ofFn,Function.comp_def] using
      (prod_rows (List.ofFn (fun j : Fin m => fun y =>
        coordinateLayer m j (rowChoices c y j))).reverse)

end BinaryCoordinateSweeps.BinarySplit

end

end OAI
