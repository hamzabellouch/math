import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseContextProgram
import OAI.Combinatorics.ContingencyTables.Machines.InitialDrawReindex

namespace OAI

/-! # The computed finite initializer used before every restart experiment -/
namespace ContingencyTables.CompanionRestartInitializer
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram DensePrograms

abbrev Prepared := CompanionPhaseContextProgram.Prepared
abbrev Input := Prepared×List Bool

def forest (z : Prepared) : RootedForestCatalog.Data := z.1.1.2.2.1
def forestRealizer : Realizer forest :=
  composition (composition (composition (composition first first) second) second) first
lemma polynomial_forest : PolynomialTime forestRealizer := by
  unfold forestRealizer
  exact polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second)
    polynomial_first

def cellInput (z : Prepared) : CompanionCellCatalog.Input :=
  (((forest z).1.2,(forest z).2),(forest z).1.1.2)
def cellInputRealizer : Realizer cellInput :=
  pair (pair (composition (f := forest) (g := fun d : RootedForestCatalog.Data => d.1.2)
      forestRealizer (composition first second))
    (composition (f := forest) (g := Prod.snd) forestRealizer second))
    (composition (f := forest) (g := fun d : RootedForestCatalog.Data => d.1.1.2)
      forestRealizer (composition (composition first first) second))
lemma polynomial_cellInput : PolynomialTime cellInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_forest (polynomial_composition polynomial_first polynomial_second))
    (polynomial_composition polynomial_forest polynomial_second))
    (polynomial_composition polynomial_forest
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second))

def fields (z : Prepared) : List ℕ := z.1.1.2.1.1.1::z.2.1
def fieldsRealizer : Realizer fields :=
  composition (f := fun z : Prepared => (z.1.1.2.1.1.1,z.2.1))
    (g := fun p : ℕ×List ℕ => p.1::p.2)
    (pair (composition (composition (composition (composition (composition first first) second) first) first) first)
      (composition second first)) listCons
lemma polynomial_fields : PolynomialTime fieldsRealizer := by
  unfold fieldsRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_first) polynomial_first) polynomial_first)
    (polynomial_composition polynomial_second polynomial_first)) polynomial_listCons

def initialBound : Expr := (.input 0)*(3*(.input 2)+1)+1
def initialExponent : Expr := 2048*((.input 3)+1)
def scalar (e : Expr) (z : Prepared) : ℕ := e.eval (fields z)
def scalarRealizer (e : Expr) : Realizer (scalar e) :=
  composition (f := fields) (g := e.eval) fieldsRealizer e.realizer
lemma polynomial_scalar (e : Expr) : PolynomialTime (scalarRealizer e) :=
  polynomial_composition polynomial_fields e.polynomial

def precision (z : Prepared) : ℕ := Nat.clog 2 (scalar initialBound z)+scalar initialExponent z
def precisionRealizer : Realizer precision :=
  composition (f := fun z : Prepared =>
    (Nat.clog 2 (scalar initialBound z),scalar initialExponent z))
    (g := fun p : ℕ×ℕ => p.1+p.2)
    (pair (composition (f := scalar initialBound) (g := Nat.clog 2)
      (scalarRealizer initialBound) ceilLogTwoRealizer) (scalarRealizer initialExponent)) add
lemma polynomial_precision : PolynomialTime precisionRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_scalar initialBound) polynomial_ceilLogTwo)
    (polynomial_scalar initialExponent)) polynomial_add

def capacities (z : Prepared) : List ℕ := CompanionCellCatalog.capacities (cellInput z)
def capacitiesRealizer : Realizer capacities :=
  composition (f := cellInput) (g := CompanionCellCatalog.capacities)
    cellInputRealizer CompanionCellCatalog.capacitiesRealizer
lemma polynomial_capacities : PolynomialTime capacitiesRealizer :=
  polynomial_composition polynomial_cellInput CompanionCellCatalog.polynomial_capacities

def width (z : Prepared) : ℕ := (InitialChoiceProgram.widths (capacities z,precision z)).sum
def widthRealizer : Realizer width :=
  composition (f := fun z : Prepared => InitialChoiceProgram.widths (capacities z,precision z))
    (g := List.sum)
    (composition (f := fun z : Prepared => (capacities z,precision z)) (g := InitialChoiceProgram.widths)
      (pair capacitiesRealizer precisionRealizer) InitialChoiceProgram.widthsRealizer) listSum
theorem polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair polynomial_capacities polynomial_precision)
    InitialChoiceProgram.polynomial_widths) polynomial_listSum

def prepare (z : Input) : CompanionComputedInitial.ProgramInput := ((cellInput z.1,precision z.1),z.2)
def prepareRealizer : Realizer prepare :=
  pair (pair (composition (f := fun z : Input => z.1) (g := cellInput) first cellInputRealizer)
    (composition (f := fun z : Input => z.1) (g := precision) first precisionRealizer)) second
lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_cellInput)
    (polynomial_composition polynomial_first polynomial_precision)) polynomial_second

def output (z : Input) : List ℕ := CompanionComputedInitial.initialProgram (prepare z)
def outputRealizer : Realizer output :=
  composition (f := prepare) (g := CompanionComputedInitial.initialProgram)
    prepareRealizer CompanionComputedInitial.initialProgramRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare CompanionComputedInitial.polynomial_initialProgram

noncomputable section
open CompanionFactorialApplication CompanionOracleDensity GridBoundary
open CompanionComputedInitial CompanionArithmeticProposal FiniteObservableTransport
open scoped BigOperators Classical
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C K H T N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : Prepared :=
  (RootedOracleWalkProgram.data A C 0 K z v,
    ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon))

lemma cellInput_data (A : Instance (Fin m) (Fin n)) (C K H T N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    cellInput (data A C K H T N R L epsilon z v)=CompanionCellCatalog.input A := rfl

lemma precision_data (A : Instance (Fin m) (Fin n)) (C K H T N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    precision (data A C K H T N R L epsilon z v)=
      CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H) := by
  simp [precision,scalar,fields,data,RootedOracleWalkProgram.data,
    initialBound,initialExponent,Expr.eval,CompanionInitialDraw.precision,CountingPhaseSchedule.initialPrecision]

lemma width_data (A : Instance (Fin m) (Fin n)) (C K H T N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    width (data A C K H T N R L epsilon z v)=
      CompanionComputedInitial.wordLength A
        (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)) := by
  unfold width capacities
  rw [cellInput_data,CompanionCellCatalog.capacities_eq,precision_data]
  rw [InitialChoiceProgram.widths_ofFn,List.sum_ofFn]
  rfl

theorem output_sameLaw (A : Instance (Fin m) (Fin n)) (C K H T N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    let B := CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)
    SameLaw (fun bits : Fin (CompanionComputedInitial.wordLength A B) → Bool =>
      output (data A C K H T N R L epsilon z v,List.ofFn bits))
      (fun bits => encodeSet (coordinateOrder A) (CompanionInitialDraw.draw A B bits).val.val) := by
  dsimp only
  have hB : 0 < CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H) := by
    unfold CompanionInitialDraw.precision CountingPhaseSchedule.initialPrecision
    omega
  have h := initialProgram_sameLaw A
    (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)) hB
  intro phi
  convert h phi using 1
  apply congrArg CommonBasesFPRAS.uniformAverage
  funext bits
  dsimp only
  rw [output,prepare,cellInput_data,precision_data]

end
end ContingencyTables.CompanionRestartInitializer

end OAI
