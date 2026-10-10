import OAI.Combinatorics.ContingencyTables.Model

namespace OAI

/-! # Complementing a bounded table

The map X ↦ b-X transforms cell minima into maxima. All margin
subtractions are justified by an actual feasible table.
-/

namespace ContingencyTables.BoundedTableComplement

open scoped BigOperators

variable {m n : ℕ}

def complement (b X : Fin m→Fin n→ℕ) (i : Fin m) (j : Fin n) : ℕ := b i j-X i j

def rowTotal (b : Fin m→Fin n→ℕ) (i : Fin m) : ℕ := ∑ j,b i j
def columnTotal (b : Fin m→Fin n→ℕ) (j : Fin n) : ℕ := ∑ i,b i j

def rows (b : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (i : Fin m) : ℕ := rowTotal b i-r i
def columns (b : Fin m→Fin n→ℕ) (c : Fin n→ℕ) (j : Fin n) : ℕ := columnTotal b j-c j

lemma complement_bounds (b X : Fin m→Fin n→ℕ) :
    ∀ i j,complement b X i j≤b i j := fun _ _=>Nat.sub_le _ _

lemma complement_twice (b X : Fin m→Fin n→ℕ) (hb : ∀ i j,X i j≤b i j) :
    complement b (complement b X)=X := by
  funext i j
  exact Nat.sub_sub_self (hb i j)

lemma complement_margins (b X : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (hm : HasMargins X r c) (hb : ∀ i j,X i j≤b i j) :
    HasMargins (complement b X) (rows b r) (columns b c) := by
  constructor
  · intro i
    have hs : (∑ j,complement b X i j)+(∑ j,X i j)=rowTotal b i := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      exact Nat.sub_add_cancel (hb i j)
    rw [hm.1 i] at hs
    unfold rows
    omega
  · intro j
    have hs : (∑ i,complement b X i j)+(∑ i,X i j)=columnTotal b j := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact Nat.sub_add_cancel (hb i j)
    rw [hm.2 j] at hs
    unfold columns
    omega

lemma row_total_ge (b X : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (hm : HasMargins X r c) (hb : ∀ i j,X i j≤b i j) (i : Fin m) :
    r i≤rowTotal b i := by
  rw [←hm.1 i]
  exact Finset.sum_le_sum (fun j _=>hb i j)

lemma column_total_ge (b X : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (hm : HasMargins X r c) (hb : ∀ i j,X i j≤b i j) (j : Fin n) :
    c j≤columnTotal b j := by
  rw [←hm.2 j]
  exact Finset.sum_le_sum (fun i _=>hb i j)

lemma margins_twice (b X : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (hm : HasMargins X r c) (hb : ∀ i j,X i j≤b i j) :
    rows b (rows b r)=r ∧ columns b (columns b c)=c := by
  constructor
  · funext i
    exact Nat.sub_sub_self (row_total_ge b X r c hm hb i)
  · funext j
    exact Nat.sub_sub_self (column_total_ge b X r c hm hb j)

lemma complement_reverse_margins (b X Y : Fin m→Fin n→ℕ)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (hx : HasMargins X r c) (hxb : ∀ i j,X i j≤b i j)
    (hy : HasMargins Y (rows b r) (columns b c)) (hyb : ∀ i j,Y i j≤b i j) :
    HasMargins (complement b Y) r c := by
  have h := complement_margins b Y (rows b r) (columns b c) hy hyb
  obtain ⟨hr,hc⟩ := margins_twice b X r c hx hxb
  rwa [hr,hc] at h

end ContingencyTables.BoundedTableComplement

end OAI
