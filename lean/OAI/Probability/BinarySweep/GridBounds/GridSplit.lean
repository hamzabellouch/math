import Mathlib
import OAI.Probability.BinarySweep.Trajectories.Trajectory

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ)

abbrev leftBits : Fin m → ℕ := fun i => bits (i.castAdd n)
abbrev rightBits : Fin n → ℕ := fun i => bits (i.natAdd m)
def leftSlot (x : GridSlot bits) : GridSlot (leftBits bits) := fun i => x (i.castAdd n)
def rightSlot (x : GridSlot bits) : GridSlot (rightBits bits) := fun i => x (i.natAdd m)
def joinSlot (x : GridSlot (leftBits bits)) (y : GridSlot (rightBits bits)) : GridSlot bits :=
  Fin.addCases x y

def slotEquiv : GridSlot bits ≃ GridSlot (leftBits bits) × GridSlot (rightBits bits) where
  toFun x := (leftSlot bits x,rightSlot bits x)
  invFun xy := joinSlot bits xy.1 xy.2
  left_inv x := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [joinSlot,leftSlot]
    | right i => simp [joinSlot,rightSlot]
  right_inv xy := by
    apply Prod.ext <;> funext i
    · simp [leftSlot,joinSlot]
    · simp [rightSlot,joinSlot]

lemma size_split : gridSize bits=gridSize (leftBits bits)*gridSize (rightBits bits) := by
  rw [← card_gridSlot, Fintype.card_congr (slotEquiv bits),Fintype.card_prod,
    card_gridSlot,card_gridSlot]

def leftTime (t : Fin (m+1)) : Fin (m+n+1) := ⟨t.val,by omega⟩
def rightTime (t : Fin (n+1)) : Fin (m+n+1) := ⟨m+t.val,by omega⟩

variable (H : PathFamily bits h)

lemma rightSlot_leftTime (t : Fin (m+1)) (k : Fin h) :
    rightSlot bits (H.position (leftTime t) k)=rightSlot bits (H.position 0 k) := by
  funext i
  unfold rightSlot
  have he := trajectory_coordinates (fun t => H.position t k)
    (fun j i hi => H.changes_only_stage j k i hi) (leftTime t) (i.natAdd m)
  rw [ite_eq_right (show ¬(i.natAdd m).val < (leftTime t).val from by
    change ¬m+i.val<t.val; omega)] at he
  exact he

lemma leftSlot_rightTime (t : Fin (n+1)) (k : Fin h) :
    leftSlot bits (H.position (rightTime t) k)=leftSlot bits (H.position (rightTime (m:=m) 0) k) := by
  funext i
  unfold leftSlot
  have he (u : Fin (n+1)) : H.position (rightTime u) k (i.castAdd n) =
      H.position (Fin.last (m+n)) k (i.castAdd n) := by
    have he := trajectory_coordinates (fun t => H.position t k)
      (fun j i hi => H.changes_only_stage j k i hi) (rightTime u) (i.castAdd n)
    rw [ite_eq_left (show (i.castAdd n).val < (rightTime u).val from by
      change i.val < m + u.val; omega)] at he
    exact he
  exact (he t).trans (he 0).symm

abbrev RowLabels (y : GridSlot (rightBits bits)) :=
  {k : Fin h // rightSlot bits (H.position 0 k)=y}
abbrev ColumnLabels (x : GridSlot (leftBits bits)) :=
  {k : Fin h // leftSlot bits (H.position (rightTime (m:=m) 0) k)=x}

noncomputable instance rowLabelsFintype (y : GridSlot (rightBits bits)) :
    Fintype (RowLabels bits H y) := Fintype.ofFinite _
noncomputable instance columnLabelsFintype (x : GridSlot (leftBits bits)) :
    Fintype (ColumnLabels bits H x) := Fintype.ofFinite _

def rowFamily (y : GridSlot (rightBits bits)) :
    PathFamily (leftBits bits) (Fintype.card (RowLabels bits H y)) where
  position t k := leftSlot bits (H.position (leftTime t) ((Fintype.equivFin (RowLabels bits H y)).symm k).val)
  disjoint t a b he := by
    apply (Fintype.equivFin (RowLabels bits H y)).symm.injective
    apply Subtype.ext
    apply H.disjoint (leftTime t)
    apply (slotEquiv bits).injective
    apply Prod.ext
    · exact he
    · change rightSlot bits (H.position (leftTime t) _) = rightSlot bits (H.position (leftTime t) _)
      simp only [rightSlot_leftTime]
      exact ((Fintype.equivFin (RowLabels bits H y)).symm a).property.trans
        ((Fintype.equivFin (RowLabels bits H y)).symm b).property.symm
  changes_only_stage j k i hi := by
    change H.position (leftTime j.succ) _ (i.castAdd n) = H.position (leftTime j.castSucc) _ (i.castAdd n)
    exact H.changes_only_stage (j.castAdd n) _ (i.castAdd n)
      (fun he => hi (Fin.ext (congrArg (fun q : Fin (m+n) => q.val) he)))

def columnFamily (x : GridSlot (leftBits bits)) :
    PathFamily (rightBits bits) (Fintype.card (ColumnLabels bits H x)) where
  position t k := rightSlot bits (H.position (rightTime t) ((Fintype.equivFin (ColumnLabels bits H x)).symm k).val)
  disjoint t a b he := by
    apply (Fintype.equivFin (ColumnLabels bits H x)).symm.injective
    apply Subtype.ext
    apply H.disjoint (rightTime t)
    apply (slotEquiv bits).injective
    apply Prod.ext
    · change leftSlot bits (H.position (rightTime t) _) = leftSlot bits (H.position (rightTime t) _)
      simp only [leftSlot_rightTime]
      exact ((Fintype.equivFin (ColumnLabels bits H x)).symm a).property.trans
        ((Fintype.equivFin (ColumnLabels bits H x)).symm b).property.symm
    · exact he
  changes_only_stage j k i hi := by
    change H.position (rightTime j.succ) _ (i.natAdd m) = H.position (rightTime j.castSucc) _ (i.natAdd m)
    exact H.changes_only_stage (j.natAdd m) _ (i.natAdd m)
      (fun he => hi (Fin.ext (by have hh := congrArg (fun q : Fin (m+n) => q.val) he; simpa using hh)))

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
variable {m n : ℕ} (bits : Fin (m+n) → ℕ)

def fillSlot {b : ℕ} (a : Fin b → ℕ) (j : Fin b) (u : GridOutside a j) : GridSlot a :=
  (Equiv.piSplitAt j (fun i => Slot (a i))).symm (fun _ => false,u)

lemma fillSlot_other {b : ℕ} (a : Fin b → ℕ) (j : Fin b) (u : GridOutside a j)
    (i : Fin b) (hi : i≠j) : fillSlot a j u i=u ⟨i,hi⟩ := by
  simp [fillSlot,Equiv.piSplitAt,hi]

def leftOutsideEquiv (j : Fin m) :
    GridOutside bits (j.castAdd n) ≃ GridSlot (rightBits bits) × GridOutside (leftBits bits) j where
  toFun u := (fun i => u ⟨i.natAdd m,by intro h; have hh := congrArg (fun q:Fin (m+n) => q.val) h; simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega⟩,
    fun i => u ⟨i.val.castAdd n,fun h => i.property (Fin.ext (congrArg (fun q:Fin (m+n) => q.val) h))⟩)
  invFun yu i := joinSlot bits (fillSlot (leftBits bits) j yu.2) yu.1 i.val
  left_inv u := by
    funext i
    rcases i with ⟨i,hi⟩
    revert hi
    induction i using Fin.addCases with
    | left i =>
      intro hi
      have hij : i≠j := fun h => hi (congrArg (Fin.castAdd n) h)
      simp only [joinSlot,Fin.addCases_left,fillSlot_other _ _ _ _ hij]
    | right i => intro hi; simp only [joinSlot,Fin.addCases_right]
  right_inv yu := by
    apply Prod.ext
    · funext i
      simp only [joinSlot,Fin.addCases_right]
    · funext i
      simp only [joinSlot,Fin.addCases_left,fillSlot_other _ _ _ _ i.property]

def rightOutsideEquiv (j : Fin n) :
    GridOutside bits (j.natAdd m) ≃ GridSlot (leftBits bits) × GridOutside (rightBits bits) j where
  toFun u := (fun i => u ⟨i.castAdd n,by intro h; have hh := congrArg (fun q:Fin (m+n) => q.val) h; simp only [Fin.val_natAdd,Fin.val_castAdd] at hh; omega⟩,
    fun i => u ⟨i.val.natAdd m,fun h => i.property (Fin.ext (by have hh := congrArg (fun q:Fin (m+n) => q.val) h; simpa using hh))⟩)
  invFun xu i := joinSlot bits xu.1 (fillSlot (rightBits bits) j xu.2) i.val
  left_inv u := by
    funext i
    rcases i with ⟨i,hi⟩
    revert hi
    induction i using Fin.addCases with
    | left i => intro hi; simp only [joinSlot,Fin.addCases_left]
    | right i =>
      intro hi
      have hij : i≠j := fun h => hi (congrArg (Fin.natAdd m) h)
      simp only [joinSlot,Fin.addCases_right,fillSlot_other _ _ _ _ hij]
  right_inv xu := by
    apply Prod.ext
    · funext i
      simp only [joinSlot,Fin.addCases_left]
    · funext i
      simp only [joinSlot,Fin.addCases_right,fillSlot_other _ _ _ _ i.property]

def rowChoices (g : GridChoices bits) (y : GridSlot (rightBits bits)) : GridChoices (leftBits bits) :=
  fun j u => g (j.castAdd n) ((leftOutsideEquiv bits j).symm (y,u))
def columnChoices (g : GridChoices bits) (x : GridSlot (leftBits bits)) : GridChoices (rightBits bits) :=
  fun j u => g (j.natAdd m) ((rightOutsideEquiv bits j).symm (x,u))

def joinChoices (L : GridSlot (rightBits bits) → GridChoices (leftBits bits))
    (R : GridSlot (leftBits bits) → GridChoices (rightBits bits)) : GridChoices bits :=
  Fin.addCases (fun j u => L ((leftOutsideEquiv bits j) u).1 j ((leftOutsideEquiv bits j) u).2)
    (fun j u => R ((rightOutsideEquiv bits j) u).1 j ((rightOutsideEquiv bits j) u).2)

def choicesEquiv : GridChoices bits ≃
    (GridSlot (rightBits bits) → GridChoices (leftBits bits)) ×
    (GridSlot (leftBits bits) → GridChoices (rightBits bits)) where
  toFun g := (rowChoices bits g,columnChoices bits g)
  invFun LR := joinChoices bits LR.1 LR.2
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

end BinaryCoordinateSweeps.GridSplit

end

end OAI
