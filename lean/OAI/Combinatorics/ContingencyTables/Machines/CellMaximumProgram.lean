import OAI.Combinatorics.ContingencyTables.Machines.CellLowerTestProgram
import OAI.Combinatorics.ContingencyTables.Machines.BinarySearchProgram

namespace OAI

/-! # Computing an attained cell maximum by binary feasibility search

A finite maximum is used only to prove the result of the executed binary
search. The program never enumerates feasible tables.
-/

namespace ContingencyTables.CellMaximumProgram

open MatchingFPRAS.TreeTyped CellLowerTestProgram
open scoped Classical

def bound (z : Context) : ℕ := ResidualGraphProgram.capacityEntry (z.1.2,z.2)

def boundRealizer : Realizer bound :=
  composition (pair (composition first second) second) ResidualGraphProgram.capacityEntryRealizer

lemma polynomial_bound : PolynomialTime boundRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second) polynomial_second)
    ResidualGraphProgram.polynomial_capacityEntry

def maximum (z : Context) : ℕ := BinarySearchProgram.search test (z,bound z)

def maximumRealizer : Realizer maximum :=
  composition (f := fun z : Context=>(z,bound z))
    (g := BinarySearchProgram.search test)
    (pair identity boundRealizer) (BinarySearchProgram.searchRealizer test testRealizer)

lemma polynomial_maximum : PolynomialTime maximumRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_bound)
    (BinarySearchProgram.polynomial_search test testRealizer polynomial_test)

lemma bound_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) :
    bound (NetworkVertexCode.data r c b,(i.val,j.val))=b i j :=
  ResidualGraphProgram.capacityEntry_code b i j

/-- For every feasible instance the computed value is attained, and it
bounds the same coordinate of every other feasible table. -/
theorem maximum_correct {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n)
    (hne : ∃ X,HasMargins X r c ∧ ∀ u v,X u v≤b u v) :
    ∃ X,HasMargins X r c ∧ (∀ u v,X u v≤b u v) ∧
      X i j=maximum (NetworkVertexCode.data r c b,(i.val,j.val)) ∧
      ∀ Y,HasMargins Y r c → (∀ u v,Y u v≤b u v) → Y i j≤X i j := by
  let S : Finset (BoundedTable r c b) := Finset.univ
  have hS : S.Nonempty := by
    obtain ⟨X,hm,hb⟩ := hne
    exact ⟨⟨⟨X,hm⟩,hb⟩,Finset.mem_univ _⟩
  obtain ⟨M,hM,hmax⟩ := Finset.exists_max_image S
    (fun X : BoundedTable r c b=>X.val.val i j) hS
  have ht (t : ℕ) :
      test ((NetworkVertexCode.data r c b,(i.val,j.val)),t)=true ↔ t≤M.val.val i j := by
    rw [CellLowerTestProgram.test_correct hEK]
    constructor
    · rintro ⟨X,hm,hb,hx⟩
      exact hx.trans (hmax ⟨⟨X,hm⟩,hb⟩ (Finset.mem_univ _))
    · intro hx
      exact ⟨M.val.val,M.val.property,M.property,hx⟩
  have he : maximum (NetworkVertexCode.data r c b,(i.val,j.val))=M.val.val i j := by
    unfold maximum
    rw [bound_code]
    exact BinarySearchProgram.search_eq test _ _ _ ht (M.property i j)
  exact ⟨M.val.val,M.val.property,M.property,he.symm,
    fun Y hm hb=>hmax ⟨⟨Y,hm⟩,hb⟩ (Finset.mem_univ _)⟩

end ContingencyTables.CellMaximumProgram

end OAI
