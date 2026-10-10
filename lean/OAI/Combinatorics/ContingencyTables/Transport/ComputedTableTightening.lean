import OAI.Combinatorics.ContingencyTables.Machines.CellMinimumProgram
import OAI.Combinatorics.ContingencyTables.Transport.TableTightening

namespace OAI

/-! # Exact table bijection for the computed attained endpoints

The endpoint hypotheses of the translation lemma are discharged by the
executed minimum and maximum searches, conditional only on EK1972.
-/

namespace ContingencyTables.ComputedTableTightening

open TableTightening
open scoped Classical

variable {m n : ℕ}

def lower (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) : ℕ :=
  CellMinimumProgram.minimum (NetworkVertexCode.data r c b,(i.val,j.val))
def upper (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) : ℕ :=
  CellMaximumProgram.maximum (NetworkVertexCode.data r c b,(i.val,j.val))

variable (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
  (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
  (hne : ∃ X,Feasible r c b X)

include hEK hne

lemma lower_le {X : Fin m→Fin n→ℕ} (hX : Feasible r c b X)
    (i : Fin m) (j : Fin n) : lower r c b i j≤X i j := by
  obtain ⟨Y,_,_,he,hy⟩ := CellMinimumProgram.minimum_correct hEK r c b i j hne
  have h := hy X hX.1 hX.2
  simpa only [he,lower] using h

lemma le_upper {X : Fin m→Fin n→ℕ} (hX : Feasible r c b X)
    (i : Fin m) (j : Fin n) : X i j≤upper r c b i j := by
  obtain ⟨Y,_,_,he,hy⟩ := CellMaximumProgram.maximum_correct hEK r c b i j hne
  have h := hy X hX.1 hX.2
  simpa only [he,upper] using h

lemma lower_attained (i : Fin m) (j : Fin n) :
    ∃ X,Feasible r c b X ∧ X i j=lower r c b i j := by
  obtain ⟨X,hm,hb,he,_⟩ := CellMinimumProgram.minimum_correct hEK r c b i j hne
  exact ⟨X,⟨hm,hb⟩,he⟩

lemma upper_attained (i : Fin m) (j : Fin n) :
    ∃ X,Feasible r c b X ∧ X i j=upper r c b i j := by
  obtain ⟨X,hm,hb,he,_⟩ := CellMaximumProgram.maximum_correct hEK r c b i j hne
  exact ⟨X,⟨hm,hb⟩,he⟩

lemma upper_le_bound (i : Fin m) (j : Fin n) : upper r c b i j≤b i j := by
  obtain ⟨X,hX,he⟩ := upper_attained hEK r c b hne i j
  simpa only [←he] using hX.2 i j

lemma lower_le_upper (i : Fin m) (j : Fin n) : lower r c b i j≤upper r c b i j := by
  obtain ⟨X,hX⟩ := hne
  exact (lower_le hEK r c b ⟨X,hX⟩ hX i j).trans
    (le_upper hEK r c b ⟨X,hX⟩ hX i j)

omit hEK hne in
def newRows : Fin m→ℕ := rows r (lower r c b)
omit hEK hne in
def newColumns : Fin n→ℕ := columns c (lower r c b)
omit hEK hne in
def newBounds : Fin m→Fin n→ℕ := bounds (lower r c b) (upper r c b)

noncomputable def tighten (X : BoundedTable r c b) :
    BoundedTable (newRows r c b) (newColumns r c b) (newBounds r c b) := by
  have h := subtract_feasible r c b (lower r c b) (upper r c b)
    (fun Y hY i j=>lower_le hEK r c b hne hY i j)
    (fun Y hY i j=>le_upper hEK r c b hne hY i j) ⟨X.val.property,X.property⟩
  exact ⟨⟨subtract X.val.val (lower r c b),h.1⟩,h.2⟩

noncomputable def restore
    (Y : BoundedTable (newRows r c b) (newColumns r c b) (newBounds r c b)) :
    BoundedTable r c b := by
  have h := add_feasible r c b (lower r c b) (upper r c b) hne
    (fun X hX i j=>lower_le hEK r c b hne hX i j)
    (upper_le_bound hEK r c b hne) ⟨Y.val.property,Y.property⟩
  exact ⟨⟨add Y.val.val (lower r c b),h.1⟩,h.2⟩

noncomputable def tighteningEquiv : BoundedTable r c b ≃
    BoundedTable (newRows r c b) (newColumns r c b) (newBounds r c b) where
  toFun := tighten hEK r c b hne
  invFun := restore hEK r c b hne
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    exact add_subtract X.val.val (lower r c b)
      (fun i j=>lower_le hEK r c b hne ⟨X.val.property,X.property⟩ i j)
  right_inv Y := by
    apply Subtype.ext
    apply Subtype.ext
    exact subtract_add Y.val.val (lower r c b)

theorem count_eq : Fintype.card (BoundedTable r c b)=
    Fintype.card (BoundedTable (newRows r c b) (newColumns r c b) (newBounds r c b)) :=
  Fintype.card_congr (tighteningEquiv hEK r c b hne)

theorem attained_endpoints :
    (∀ i j,∃ Y,HasMargins Y (newRows r c b) (newColumns r c b) ∧
      (∀ a d,Y a d≤newBounds r c b a d) ∧ Y i j=0) ∧
    (∀ i j,∃ Y,HasMargins Y (newRows r c b) (newColumns r c b) ∧
      (∀ a d,Y a d≤newBounds r c b a d) ∧ Y i j=newBounds r c b i j) := by
  have h := endpoints r c b (lower r c b) (upper r c b)
    (fun X hX i j=>lower_le hEK r c b hne hX i j)
    (fun X hX i j=>le_upper hEK r c b hne hX i j)
    (lower_attained hEK r c b hne) (upper_attained hEK r c b hne)
  simpa only [TightFeasible,and_assoc,newRows,newColumns,newBounds] using h

end ContingencyTables.ComputedTableTightening

end OAI
