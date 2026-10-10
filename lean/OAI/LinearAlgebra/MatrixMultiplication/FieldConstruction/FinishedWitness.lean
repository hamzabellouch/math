import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.MatrixMapDecidable
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.FinalState
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.InitialZeroFinish
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ZeroFinish
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.StageCFinish
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.Terminal

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldFinishedWitness

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open AllFieldTerminalStatisticLaws AllFieldTerminalRates
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

private def localMapWithFintypes {F : Type*} [Field F]
    {X Y Z X' Y' Z' : Type} [newX : Fintype X] [newY : Fintype Y] [newZ : Fintype Z]
    {oldX : Fintype X} {oldY : Fintype Y} {oldZ : Fintype Z}
    {T : Tensor F X Y Z} {Q : Tensor F X' Y' Z'}
    (M : @LocalMap F _ X Y Z X' Y' Z' oldX oldY oldZ T Q) :
    @LocalMap F _ X Y Z X' Y' Z' newX newY newZ T Q := by
  cases Subsingleton.elim oldX newX
  cases Subsingleton.elim oldY newY
  cases Subsingleton.elim oldZ newZ
  exact M

private def matrixProductMap (F : Type*) [Field F]
    (A B C D E G : Type) [Fintype A] [Fintype B] [Fintype C]
    [Fintype D] [Fintype E] [Fintype G] :
    LocalMap (Tensor.product (Tensor.matrixCoefficients (K := F) A B C)
      (Tensor.matrixCoefficients D E G))
      (Tensor.matrixCoefficients (A × D) (B × E) (C × G)) := by
  apply LocalMap.ofExists
  refine ⟨_, _, _, (Tensor.pullback_eq_restrict
    (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
    (fun y : (B × E) × (C × G) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
    (fun z : (C × G) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2))) _).symm.trans ?_⟩
  funext x y z
  exact Tensor.matrixCoefficients_product x y z

private def combineMatrixMaps {F : Type*} [Field F]
    {X Y Z U V W A B C D E G : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype G]
    {T : Tensor F X Y Z} {Q : Tensor F U V W}
    (first : LocalMap T (Tensor.matrixCoefficients A B C))
    (second : LocalMap Q (Tensor.matrixCoefficients D E G)) :
    LocalMap (Tensor.product T Q)
      (Tensor.matrixCoefficients (A × D) (B × E) (C × G)) :=
  (first.product second).comp (matrixProductMap F A B C D E G)

variable {K : ℕ} (allocation : Allocation) (m : ℕ)

abbrev ZeroRows := ∀ h : TerminalZero K, AllFieldZeroFinish.Row allocation m h
abbrev ZeroMiddles := ∀ h : TerminalZero K, AllFieldZeroFinish.Middle allocation m h
abbrev ZeroColumns := ∀ h : TerminalZero K, AllFieldZeroFinish.Column allocation m h

abbrev Rows := AllFieldInitialZeroFinish.Rows (K := K) allocation (terminalDilation K m) ×
  (ZeroRows (K := K) allocation m ×
    AllFieldStageCFinish.Rows (K := K) allocation (terminalDilation K m))
abbrev Middles := AllFieldInitialZeroFinish.Middles (K := K) allocation (terminalDilation K m) ×
  (ZeroMiddles (K := K) allocation m ×
    AllFieldStageCFinish.Middles (K := K) allocation (terminalDilation K m))
abbrev Columns := AllFieldInitialZeroFinish.Columns (K := K) allocation (terminalDilation K m) ×
  (ZeroColumns (K := K) allocation m ×
    AllFieldStageCFinish.Columns (K := K) allocation (terminalDilation K m))

local instance initialRowsFintype :
    Fintype (AllFieldInitialZeroFinish.Rows (K := K) allocation (terminalDilation K m)) := by
  letI : DecidableEq (AllFieldInitialZeroFinish.Index K) := Classical.decEq _
  exact inferInstanceAs (Fintype (∀ h : AllFieldInitialZeroFinish.Index K,
    AllFieldInitialZeroFinish.RowIndex allocation (terminalDilation K m) h))

local instance initialMiddlesFintype :
    Fintype (AllFieldInitialZeroFinish.Middles (K := K) allocation (terminalDilation K m)) := by
  letI : DecidableEq (AllFieldInitialZeroFinish.Index K) := Classical.decEq _
  exact inferInstanceAs (Fintype (∀ h : AllFieldInitialZeroFinish.Index K,
    AllFieldInitialZeroFinish.MiddleIndex allocation (terminalDilation K m) h))

local instance initialColumnsFintype :
    Fintype (AllFieldInitialZeroFinish.Columns (K := K) allocation (terminalDilation K m)) := by
  letI : DecidableEq (AllFieldInitialZeroFinish.Index K) := Classical.decEq _
  exact inferInstanceAs (Fintype (∀ h : AllFieldInitialZeroFinish.Index K,
    AllFieldInitialZeroFinish.ColumnIndex allocation (terminalDilation K m) h))

local instance stageCRowsFintype :
    Fintype (AllFieldStageCFinish.Rows (K := K) allocation (terminalDilation K m)) := by
  exact inferInstanceAs (Fintype (∀ h : CWStageCProducts.PopulationHistory K,
    CWStageCProducts.RowWords (CWStageCProducts.populationSide h)
      (CWStageCProducts.populationAtomCounts allocation (terminalDilation K m) h)))

local instance stageCMiddlesFintype :
    Fintype (AllFieldStageCFinish.Middles (K := K) allocation (terminalDilation K m)) := by
  exact inferInstanceAs (Fintype (∀ h : CWStageCProducts.PopulationHistory K,
    CWStageCProducts.MiddleWords (CWStageCProducts.populationSide h)
      (CWStageCProducts.populationAtomCounts allocation (terminalDilation K m) h)))

local instance stageCColumnsFintype :
    Fintype (AllFieldStageCFinish.Columns (K := K) allocation (terminalDilation K m)) := by
  exact inferInstanceAs (Fintype (∀ h : CWStageCProducts.PopulationHistory K,
    CWStageCProducts.ColumnWords (CWStageCProducts.populationSide h)
      (CWStageCProducts.populationAtomCounts allocation (terminalDilation K m) h)))

local instance rowsFintype : Fintype (Rows (K := K) allocation m) :=
  inferInstanceAs (Fintype
    (AllFieldInitialZeroFinish.Rows (K := K) allocation (terminalDilation K m) ×
      (ZeroRows (K := K) allocation m ×
        AllFieldStageCFinish.Rows (K := K) allocation (terminalDilation K m))))

local instance middlesFintype : Fintype (Middles (K := K) allocation m) :=
  inferInstanceAs (Fintype
    (AllFieldInitialZeroFinish.Middles (K := K) allocation (terminalDilation K m) ×
      (ZeroMiddles (K := K) allocation m ×
        AllFieldStageCFinish.Middles (K := K) allocation (terminalDilation K m))))

local instance columnsFintype : Fintype (Columns (K := K) allocation m) :=
  inferInstanceAs (Fintype
    (AllFieldInitialZeroFinish.Columns (K := K) allocation (terminalDilation K m) ×
      (ZeroColumns (K := K) allocation m ×
        AllFieldStageCFinish.Columns (K := K) allocation (terminalDilation K m))))

local instance initialRawFintype :
    Fintype (AllFieldFinalState.InitialWords (K := K) allocation (terminalDilation K m)) :=
  inferInstanceAs (Fintype (∀ h : AllFieldFinalState.InitialIndex K,
    HistoryWord allocation (terminalDilation K m) (.initial h.1.val, h.2)))

local instance zeroRawFintype :
    Fintype (AllFieldFinalState.ZeroWords (K := K) allocation (terminalDilation K m)) :=
  inferInstanceAs (Fintype (∀ h : TerminalZero K,
    HistoryWord allocation (terminalDilation K m) (AllFieldTerminalStatisticLaws.history h)))

local instance stageCRawFintype :
    Fintype (AllFieldFinalState.CWords (K := K) allocation (terminalDilation K m)) :=
  inferInstanceAs (Fintype (∀ h : AllFieldFinalState.CIndex K,
    HistoryWord allocation (terminalDilation K m) (.afterC h.1, h.2)))

theorem zero_volume :
    Fintype.card (ZeroRows (K := K) allocation m) *
      Fintype.card (ZeroMiddles (K := K) allocation m) *
        Fintype.card (ZeroColumns (K := K) allocation m) = zeroVolume (K := K) allocation m := by
  simp only [ZeroRows, ZeroMiddles, ZeroColumns, Fintype.card_pi, zeroVolume]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun h _ => AllFieldZeroFinish.volume allocation m h

theorem volume_eq :
    Fintype.card (Rows (K := K) allocation m) *
      Fintype.card (Middles (K := K) allocation m) *
        Fintype.card (Columns (K := K) allocation m) = terminalVolume (K := K) allocation m := by
  simp only [Rows, Middles, Columns, Fintype.card_prod]
  calc
    _ = (Fintype.card (AllFieldInitialZeroFinish.Rows (K := K) allocation (terminalDilation K m)) *
          Fintype.card (AllFieldInitialZeroFinish.Middles (K := K) allocation (terminalDilation K m)) *
          Fintype.card (AllFieldInitialZeroFinish.Columns (K := K) allocation (terminalDilation K m))) *
        (Fintype.card (ZeroRows (K := K) allocation m) *
          Fintype.card (ZeroMiddles (K := K) allocation m) *
          Fintype.card (ZeroColumns (K := K) allocation m)) *
        (Fintype.card (AllFieldStageCFinish.Rows (K := K) allocation (terminalDilation K m)) *
          Fintype.card (AllFieldStageCFinish.Middles (K := K) allocation (terminalDilation K m)) *
          Fintype.card (AllFieldStageCFinish.Columns (K := K) allocation (terminalDilation K m))) := by ring
    _ = _ := by rw [AllFieldInitialZeroFinish.volume_eq, zero_volume,
      AllFieldStageCFinish.volume_eq_populationVolume]; rfl

theorem dimensions_pos :
    0 < Fintype.card (Rows (K := K) allocation m) ∧
      0 < Fintype.card (Middles (K := K) allocation m) ∧
        0 < Fintype.card (Columns (K := K) allocation m) := by
  have hp := terminalVolume_pos (K := K) allocation m
  rw [← volume_eq allocation m] at hp
  have hab := Nat.pos_of_mul_pos_right hp
  exact ⟨Nat.pos_of_mul_pos_right hab, Nat.pos_of_mul_pos_left hab,
    Nat.pos_of_mul_pos_left hp⟩

def zeroMap (F : Type*) [Field F] {ε : ℝ} (hm : 0 < m) (hε : 0 ≤ ε) :
    LocalMap (AllFieldFinalState.zeroTensor (K := K) allocation (terminalDilation K m) F ε)
      (Tensor.matrixCoefficients (ZeroRows (K := K) allocation m)
        (ZeroMiddles (K := K) allocation m) (ZeroColumns (K := K) allocation m)) := by
  let result := AllFieldTerminal.terminalProductMap
    (fun h : TerminalZero K => historyTensor F allocation (terminalDilation K m) ε
      (AllFieldTerminalStatisticLaws.history h))
    (fun h => AllFieldZeroFinish.Row allocation m h)
    (fun h => AllFieldZeroFinish.Middle allocation m h)
    (fun h => AllFieldZeroFinish.Column allocation m h)
    (fun h => LocalMap.redecideMatrix
      (AllFieldZeroFinish.localMap F allocation hm hε h) _ _ _)
  let aligned := localMapWithFintypes (F := F)
    (X := AllFieldFinalState.ZeroWords (K := K) allocation (terminalDilation K m))
    (Y := AllFieldFinalState.ZeroWords (K := K) allocation (terminalDilation K m))
    (Z := AllFieldFinalState.ZeroWords (K := K) allocation (terminalDilation K m))
    (newX := inferInstance) (newY := inferInstance) (newZ := inferInstance) result
  exact LocalMap.redecideMatrix aligned _ _ _

def terminalMap (F : Type*) [Field F] {ε : ℝ} (hm : 0 < m) (hε : 0 ≤ ε) :
    LocalMap (stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2))
      (Tensor.matrixCoefficients (Rows (K := K) allocation m)
        (Middles (K := K) allocation m) (Columns (K := K) allocation m)) := by
  let initialAligned := localMapWithFintypes (F := F)
    (X := AllFieldInitialZeroFinish.RawWords (K := K) allocation (terminalDilation K m))
    (Y := AllFieldInitialZeroFinish.RawWords (K := K) allocation (terminalDilation K m))
    (Z := AllFieldInitialZeroFinish.RawWords (K := K) allocation (terminalDilation K m))
    (newX := inferInstance) (newY := inferInstance) (newZ := inferInstance)
    (AllFieldInitialZeroFinish.finishMap (K := K) allocation (terminalDilation K m) F ε)
  let initial := LocalMap.redecideMatrix initialAligned
    (Classical.decEq _) (Classical.decEq _) (Classical.decEq _)
  let zeros := LocalMap.redecideMatrix (zeroMap (K := K) allocation m F hm hε)
    (Classical.decEq _) (Classical.decEq _) (Classical.decEq _)
  let interior := LocalMap.redecideMatrix
    (AllFieldStageCFinish.finishMap (K := K) allocation (terminalDilation K m) F ε)
    (Classical.decEq _) (Classical.decEq _) (Classical.decEq _)
  let second := LocalMap.redecideMatrix
    (combineMatrixMaps zeros interior)
    (Classical.decEq _) (Classical.decEq _) (Classical.decEq _)
  let third := combineMatrixMaps initial second
  exact LocalMap.redecideMatrix
    ((AllFieldFinalState.map (K := K) allocation (terminalDilation K m) F ε).comp third) _ _ _

variable {F : Type*} [Field F] {ε : ℝ} {I : Type} [Fintype I]

def execution (hm : 0 < m) (hε : 0 ≤ ε)
    (E : Execution (cwSource F K (terminalLength allocation K m))
      (Tensor.directSum (fun _ : I =>
        stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2)))) :
    Execution (cwSource F K (terminalLength allocation K m))
      (AllFieldSource.matrixTarget F (Fintype.card (Rows (K := K) allocation m))
        (Fintype.card (Middles (K := K) allocation m))
        (Fintype.card (Columns (K := K) allocation m)) (Fintype.card I)) :=
  (E.restrict _ ((terminalMap allocation m F hm hε).parallelCopies I)).restrict _
    (LocalMap.ofExists (TerminalRelabel.directSum_matrix_restrict_fin (K := F)
      I (Rows (K := K) allocation m) (Middles (K := K) allocation m)
        (Columns (K := K) allocation m)))

def witness (hm : 0 < m) (hε : 0 ≤ ε)
    (E : Execution (cwSource F K (terminalLength allocation K m))
      (Tensor.directSum (fun _ : I =>
        stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2))))
    (hI : 0 < Fintype.card I) : AllFieldWitness F :=
  (execution allocation m hm hε E).toWitness
    (dimensions_pos allocation m).1 (dimensions_pos allocation m).2.1
    (dimensions_pos allocation m).2.2 hI

@[simp] theorem witness_volume (hm : 0 < m) (hε : 0 ≤ ε)
    (E : Execution (cwSource F K (terminalLength allocation K m))
      (Tensor.directSum (fun _ : I =>
        stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2))))
    (hI : 0 < Fintype.card I) :
    (witness allocation m hm hε E hI).volume = terminalVolume (K := K) allocation m :=
  volume_eq allocation m

@[simp] theorem witness_multiplicity (hm : 0 < m) (hε : 0 ≤ ε)
    (E : Execution (cwSource F K (terminalLength allocation K m))
      (Tensor.directSum (fun _ : I =>
        stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2))))
    (hI : 0 < Fintype.card I) :
    (witness allocation m hm hε E hI).multiplicity = Fintype.card I := rfl

@[simp] theorem witness_rankBound (hm : 0 < m) (hε : 0 ≤ ε)
    (E : Execution (cwSource F K (terminalLength allocation K m))
      (Tensor.directSum (fun _ : I =>
        stateTensor F (K := K) allocation (terminalDilation K m) ε (K + 2))))
    (hI : 0 < Fintype.card I) :
    (witness allocation m hm hε E hI).rankBound =
      AllFieldSource.rankBudget E.Copies K (terminalLength allocation K m) := rfl

end MatrixMultiplication.AllFieldFinishedWitness

end

end OAI
