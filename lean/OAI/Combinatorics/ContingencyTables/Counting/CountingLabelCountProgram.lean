import OAI.Combinatorics.ContingencyTables.Rooted.RootedForestCatalog

namespace OAI

/-! # Executing the actual number of factorial labels

Only retained capacities are summed; the program does not expand any
capacity into a list of labels to obtain the phase controls.
-/

namespace ContingencyTables.CountingLabelCountProgram
open MatchingFPRAS.TreeTyped

abbrev Input := RootedForestCatalog.Data

def catalogInput (z : Input) : CompanionCellCatalog.Input := ((z.1.2,z.2),z.1.1.2)
def catalogInputRealizer : Realizer catalogInput :=
  pair (pair (composition first second) second) (composition (composition first first) second)
lemma polynomial_catalogInput : PolynomialTime catalogInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    polynomial_second) (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second)

def capacities (z : Input) : List ℕ := CompanionCellCatalog.capacities (catalogInput z)
def capacitiesRealizer : Realizer capacities :=
  composition (f := catalogInput) (g := CompanionCellCatalog.capacities)
    catalogInputRealizer CompanionCellCatalog.capacitiesRealizer
lemma polynomial_capacities : PolynomialTime capacitiesRealizer :=
  polynomial_composition polynomial_catalogInput CompanionCellCatalog.polynomial_capacities

def count (z : Input) : ℕ := (capacities z).sum
def countRealizer : Realizer count :=
  composition (f := capacities) (g := List.sum) capacitiesRealizer listSum
lemma polynomial_count : PolynomialTime countRealizer :=
  polynomial_composition polynomial_capacities polynomial_listSum

open CompanionFactorialApplication
open scoped BigOperators Classical
variable {m n : ℕ}

lemma catalogInput_data (A : Instance (Fin m) (Fin n)) :
    catalogInput (RootedForestCatalog.data A)=CompanionCellCatalog.input A := rfl

lemma count_data (A : Instance (Fin m) (Fin n)) :
    count (RootedForestCatalog.data A)=Fintype.card (Labels A) := by
  rw [count,capacities,catalogInput_data,CompanionCellCatalog.capacities_eq,List.sum_ofFn]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fintype.sum_equiv (CompanionCellCatalog.cellEquiv A) _ _ (fun _ => rfl)

lemma count_bound (A : Instance (Fin m) (Fin n)) :
    Fintype.card (Labels A) ≤ A.d*A.W := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    (∑ s : SmallCell A,A.b s.val.1 s.val.2) ≤ ∑ _s : SmallCell A,A.W :=
      Finset.sum_le_sum (fun s _ => (A.hsmall _ _ s.property).le)
    _ = Fintype.card (SmallCell A)*A.W := by simp
    _ ≤ A.d*A.W := Nat.mul_le_mul_right A.W
      ((Fintype.card_subtype_le (fun a : Fin m×Fin n => A.small a.1 a.2=true)).trans
        (by simpa only [Fintype.card_prod] using A.hcard))

end ContingencyTables.CountingLabelCountProgram

end OAI
