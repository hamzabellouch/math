import OAI.Combinatorics.ContingencyTables.Model

namespace OAI

/-! # Simultaneous tightening and translation by attained cell minima

The hypotheses here are exactly the extremum properties proved for the
executed searches. The maps preserve all tables, with explicit inverse
addition and with both endpoints of every translated interval attained.
-/

namespace ContingencyTables.TableTightening

open scoped BigOperators

variable {m n : ℕ}

def subtract (X l : Fin m→Fin n→ℕ) (i : Fin m) (j : Fin n) : ℕ := X i j-l i j
def add (Y l : Fin m→Fin n→ℕ) (i : Fin m) (j : Fin n) : ℕ := Y i j+l i j

def rows (r : Fin m→ℕ) (l : Fin m→Fin n→ℕ) (i : Fin m) : ℕ := r i-∑ j,l i j
def columns (c : Fin n→ℕ) (l : Fin m→Fin n→ℕ) (j : Fin n) : ℕ := c j-∑ i,l i j

def bounds (l u : Fin m→Fin n→ℕ) (i : Fin m) (j : Fin n) : ℕ := u i j-l i j

lemma add_subtract (X l : Fin m→Fin n→ℕ) (hl : ∀ i j,l i j≤X i j) :
    add (subtract X l) l=X := by
  funext i j
  exact Nat.sub_add_cancel (hl i j)

lemma subtract_add (Y l : Fin m→Fin n→ℕ) : subtract (add Y l) l=Y := by
  funext i j
  exact Nat.add_sub_cancel _ _

lemma subtract_margins (X l : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (hm : HasMargins X r c) (hl : ∀ i j,l i j≤X i j) :
    HasMargins (subtract X l) (rows r l) (columns c l) := by
  constructor
  · intro i
    have he : (∑ j,subtract X l i j)+(∑ j,l i j)=r i := by
      rw [←Finset.sum_add_distrib,←hm.1 i]
      apply Finset.sum_congr rfl
      intro j _
      exact Nat.sub_add_cancel (hl i j)
    unfold rows
    omega
  · intro j
    have he : (∑ i,subtract X l i j)+(∑ i,l i j)=c j := by
      rw [←Finset.sum_add_distrib,←hm.2 j]
      apply Finset.sum_congr rfl
      intro i _
      exact Nat.sub_add_cancel (hl i j)
    unfold columns
    omega

lemma lower_sums (X l : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (hm : HasMargins X r c) (hl : ∀ i j,l i j≤X i j) :
    (∀ i,(∑ j,l i j)≤r i) ∧ (∀ j,(∑ i,l i j)≤c j) := by
  constructor
  · intro i
    rw [←hm.1 i]
    exact Finset.sum_le_sum (fun j _=>hl i j)
  · intro j
    rw [←hm.2 j]
    exact Finset.sum_le_sum (fun i _=>hl i j)

lemma add_margins (Y l : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (hr : ∀ i,(∑ j,l i j)≤r i) (hc : ∀ j,(∑ i,l i j)≤c j)
    (hm : HasMargins Y (rows r l) (columns c l)) : HasMargins (add Y l) r c := by
  constructor
  · intro i
    simpa only [add,Finset.sum_add_distrib,hm.1 i,rows] using Nat.sub_add_cancel (hr i)
  · intro j
    simpa only [add,Finset.sum_add_distrib,hm.2 j,columns] using Nat.sub_add_cancel (hc j)

variable (r : Fin m→ℕ) (c : Fin n→ℕ) (b l u : Fin m→Fin n→ℕ)

def Feasible (X : Fin m→Fin n→ℕ) : Prop := HasMargins X r c ∧ ∀ i j,X i j≤b i j

def TightFeasible (Y : Fin m→Fin n→ℕ) : Prop :=
  HasMargins Y (rows r l) (columns c l) ∧ ∀ i j,Y i j≤bounds l u i j

/-- A feasible table lies in every attained coordinate interval. -/
theorem subtract_feasible (hl : ∀ X,Feasible r c b X→∀ i j,l i j≤X i j)
    (hu : ∀ X,Feasible r c b X→∀ i j,X i j≤u i j)
    {X : Fin m→Fin n→ℕ} (hX : Feasible r c b X) :
    TightFeasible r c l u (subtract X l) := by
  refine ⟨subtract_margins X l r c hX.1 (hl X hX),?_⟩
  intro i j
  exact Nat.sub_le_sub_right (hu X hX i j) (l i j)

theorem add_feasible (hne : ∃ X,Feasible r c b X)
    (hl : ∀ X,Feasible r c b X→∀ i j,l i j≤X i j)
    (hu : ∀ i j,u i j≤b i j)
    {Y : Fin m→Fin n→ℕ} (hY : TightFeasible r c l u Y) :
    Feasible r c b (add Y l) := by
  obtain ⟨X,hX⟩ := hne
  have hs := lower_sums X l r c hX.1 (hl X hX)
  refine ⟨add_margins Y l r c hs.1 hs.2 hY.1,?_⟩
  intro i j
  have hlo := (hl X hX i j).trans (hX.2 i j)
  have hbound := hY.2 i j
  change Y i j≤u i j-l i j at hbound
  change Y i j+l i j≤b i j
  have hup := hu i j
  omega

/-- Both translated endpoints are actual table entries, including when
an interval has width zero. -/
theorem endpoints (hl : ∀ X,Feasible r c b X→∀ i j,l i j≤X i j)
    (hu : ∀ X,Feasible r c b X→∀ i j,X i j≤u i j)
    (hlo : ∀ i j,∃ X,Feasible r c b X ∧ X i j=l i j)
    (hup : ∀ i j,∃ X,Feasible r c b X ∧ X i j=u i j) :
    (∀ i j,∃ Y,TightFeasible r c l u Y ∧ Y i j=0) ∧
      (∀ i j,∃ Y,TightFeasible r c l u Y ∧ Y i j=bounds l u i j) := by
  constructor
  · intro i j
    obtain ⟨X,hX,he⟩ := hlo i j
    refine ⟨subtract X l,subtract_feasible r c b l u hl hu hX,?_⟩
    simp only [subtract,he,Nat.sub_self]
  · intro i j
    obtain ⟨X,hX,he⟩ := hup i j
    refine ⟨subtract X l,subtract_feasible r c b l u hl hu hX,?_⟩
    simp only [subtract,he,bounds]

end ContingencyTables.TableTightening

end OAI
