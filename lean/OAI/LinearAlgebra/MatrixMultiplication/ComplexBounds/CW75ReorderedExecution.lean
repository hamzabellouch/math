import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.ComplexCW75InitialExecution
import OAI.LinearAlgebra.MatrixMultiplication.ComplexBounds.CW75ReorderedWords
import OAI.LinearAlgebra.MatrixMultiplication.ComplexBounds.CW75ReorderedGeometricValues
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexConditionalHierarchyStage
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexOrientedConditionalHierarchyStage
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexGeometricStageCoordinates
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialExecutionReindex

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedExecution

open MatrixMultiplication.Foundation
open CW75LabelHierarchy CW75ReorderedWords ConditionalPrefixWords ComplexWitness
open PolynomialKernelExecution ExecutionPairingBudget StageHierarchyResources
open scoped BigOperators Classical

attribute [local irreducible] CW75LabelHierarchy.retainedWords

abbrev Position (counts : Scalar → ℕ) (t : ℕ) := BlockPosition counts t
abbrev Coordinate (counts : Scalar → ℕ) (t : ℕ) := LongWord (Position counts t)
abbrev Prefix (counts : Scalar → ℕ) (t n : ℕ) :=
  ExactPrefix counts curveLabels n t (Position counts t)

def readerPair : ℕ → ReaderPair
  | 1 => .xz
  | 3 | 4 => .yz
  | _ => .xy

def pairingProduct (counts : Scalar → ℕ) (t : ℕ) (pair : ReaderPair) (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, if readerPair i = pair then
    stageRefinementCount counts curveLabels i t else 1

@[simp] theorem pairingProduct_zero (counts : Scalar → ℕ) (t : ℕ) (pair : ReaderPair) :
    pairingProduct counts t pair 0 = 1 := by simp [pairingProduct]

theorem pairingProduct_succ (counts : Scalar → ℕ) (t : ℕ) (pair : ReaderPair) (n : ℕ) :
    pairingProduct counts t pair (n + 1) = pairingProduct counts t pair n *
      (if readerPair n = pair then stageRefinementCount counts curveLabels n t else 1) := by
  simp only [pairingProduct, Finset.prod_range_succ]

def prefixValue {PX PY PZ : Type*} (counts : Scalar → ℕ) (t n : ℕ)
    (pairing : Tensor ℂ PX PY PZ) :
    Tensor ℂ (Coordinate counts t × (Prefix counts t n × PX))
      (Coordinate counts t × (Prefix counts t n × PY))
      (Coordinate counts t × (Prefix counts t n × PZ)) :=
  fun x y z => if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
      eligible id x.2.1 x.1 y.1 z.1 then pairing x.2.2 y.2.2 z.2.2 else 0

structure Bundle (counts : Scalar → ℕ) (t n : ℕ) where
  PX : Type
  PY : Type
  PZ : Type
  AX : Type
  AY : Type
  AZ : Type
  [finitePX : Fintype PX]
  [finitePY : Fintype PY]
  [finitePZ : Fintype PZ]
  [finiteAX : Fintype AX]
  [finiteAY : Fintype AY]
  [finiteAZ : Fintype AZ]
  execution : Execution (Coordinate counts t) (Coordinate counts t) (Coordinate counts t)
    (Prefix counts t n) PX PY PZ AX AY AZ
      (CW75InitialExecution.support (N := t * ∑ a, counts a))
  shape : MatrixCoordinates PX PY PZ
  shape_positive : shape.Positive
  normal : execution.value = prefixValue counts t n shape.tensor
  rank_exact : execution.rankBound = stageAuxiliaryBudget counts curveLabels n t
  volume_exact : shape.volume = stagePairingProduct counts curveLabels n t
  rows_exact : shape.rows = pairingProduct counts t .xz n
  inner_exact : shape.inner = pairingProduct counts t .xy n
  columns_exact : shape.columns = pairingProduct counts t .yz n
  pairing_budget : shape.volume ≤ execution.rankBound

attribute [instance] Bundle.finitePX Bundle.finitePY Bundle.finitePZ
attribute [instance] Bundle.finiteAX Bundle.finiteAY Bundle.finiteAZ

theorem position_card (counts : Scalar → ℕ) (t : ℕ) :
    Fintype.card (Position counts t) = ∑ a, t * counts a := by
  simp [Position, BlockPosition, Finset.mul_sum]

def initial (counts : Scalar → ℕ) (t : ℕ) : Bundle counts t 0 := by
  let E := (CW75InitialExecution.execution (t * ∑ a, counts a)).reindexOutput
    (rootPrefixEquiv counts curveLabels t (Position counts t) (position_card counts t))
    (Equiv.refl PUnit) (Equiv.refl PUnit) (Equiv.refl PUnit)
  refine {
    PX := PUnit
    PY := PUnit
    PZ := PUnit
    AX := PUnit
    AY := PUnit
    AZ := PUnit
    execution := E
    shape := MatrixCoordinates.scalar
    shape_positive := MatrixCoordinates.scalar_positive
    normal := ?_
    rank_exact := ?_
    volume_exact := ?_
    rows_exact := by simp [MatrixCoordinates.scalar]
    inner_exact := by simp [MatrixCoordinates.scalar]
    columns_exact := by simp [MatrixCoordinates.scalar]
    pairing_budget := le_rfl
  }
  · funext x y z
    change E.value x y z = prefixValue counts t 0 MatrixCoordinates.scalar.tensor x y z
    rw [Execution.reindexOutput_value, CW75InitialExecution.value_retained]
    have hxy : x.2.1 = y.2.1 := Subsingleton.elim _ _
    have hxz : x.2.1 = z.2.1 := Subsingleton.elim _ _
    have hguard : (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        eligible id x.2.1 x.1 y.1 z.1) ↔
        ∀ i, CW75Primitive.tensor (x.1 i) (y.1 i) (z.1 i) ≠ 0 := by
      rw [root_eligible_iff]
      exact ⟨fun h => h.2.2, fun h => ⟨hxy, hxz, h⟩⟩
    simp only [prefixValue, hguard, MatrixCoordinates.scalar_tensor]
  · change 1 = stageAuxiliaryBudget counts curveLabels 0 t
    simp [stageAuxiliaryBudget]
  · change 1 = stagePairingProduct counts curveLabels 0 t
    simp [stagePairingProduct]

theorem previous_eligible {counts : Scalar → ℕ} {t n : ℕ} (B : Bundle counts t n)
    (x : Coordinate counts t × (Prefix counts t n × B.PX))
    (y : Coordinate counts t × (Prefix counts t n × B.PY))
    (z : Coordinate counts t × (Prefix counts t n × B.PZ))
    (_hs : CW75InitialExecution.support (N := t * ∑ a, counts a) x.1 y.1 z.1)
    (hn : B.execution.value x y z ≠ 0) : eligible id x.2.1 x.1 y.1 z.1 := by
  rw [B.normal] at hn
  by_contra h
  exact hn (by simp [prefixValue, h])

section Successor

variable {counts : Scalar → ℕ} {t n : ℕ} (B : Bundle counts t n)
variable {NX NY NZ BX BY BZ : Type}
variable [Fintype BX] [Fintype BY] [Fintype BZ]

def refinedExecution
    (S : Stage B.execution (Fin (stageRefinementCount counts curveLabels n t))
      NX NY NZ BX BY BZ) :
    Execution (Coordinate counts t) (Coordinate counts t) (Coordinate counts t)
      (Prefix counts t (n + 1)) (B.PX × NX) (B.PY × NY) (B.PZ × NZ)
      (B.AX × BX) (B.AY × BY) (B.AZ × BZ)
      (CW75InitialExecution.support (N := t * ∑ a, counts a)) :=
  (B.execution.step S).reindexOutput
    (nextPrefixEquiv counts curveLabels n t (Position counts t))
    (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)

theorem refinedExecution_normal
    (S : Stage B.execution (Fin (stageRefinementCount counts curveLabels n t))
      NX NY NZ BX BY BZ)
    (shape : MatrixCoordinates NX NY NZ)
    (hstage : ∀ p x y z, eligible id p x.1 y.1 z.1 →
      S.value p x y z = if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible id (appendCode p x.2.1) x.1 y.1 z.1
        then shape.tensor x.2.2 y.2.2 z.2.2 else 0) :
    (refinedExecution B S).value =
      prefixValue counts t (n + 1) (B.shape.product shape).tensor := by
  classical
  funext x y z
  let e := nextPrefixEquiv counts curveLabels n t (Position counts t)
  let px := e x.2.1
  let py := e y.2.1
  let pz := e z.2.1
  have hdecode (p : Prefix counts t (n + 1)) :
      appendCode (e p).1 (e p).2 = p := e.symm_apply_apply p
  change B.execution.value (x.1, (px.1, x.2.2.1))
      (y.1, (py.1, y.2.2.1)) (z.1, (pz.1, z.2.2.1)) *
    S.value px.1 (x.1, (px.2, x.2.2.2))
      (y.1, (py.2, y.2.2.2)) (z.1, (pz.2, z.2.2.2)) = _
  rw [B.normal]
  simp only [prefixValue]
  by_cases hold : px.1 = py.1 ∧ px.1 = pz.1 ∧ eligible id px.1 x.1 y.1 z.1
  · rw [ite_eq_left hold]
    have hguard :
        (px.2 = py.2 ∧ px.2 = pz.2 ∧ eligible id (appendCode px.1 px.2) x.1 y.1 z.1) ↔
        (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧ eligible id x.2.1 x.1 y.1 z.1) := by
      constructor
      · rintro ⟨hxy, hxz, he⟩
        refine ⟨e.injective (Prod.ext hold.1 hxy),
          e.injective (Prod.ext hold.2.1 hxz), ?_⟩
        simpa only [px, hdecode] using he
      · rintro ⟨hxy, hxz, he⟩
        refine ⟨congrArg (fun p => (e p).2) hxy,
          congrArg (fun p => (e p).2) hxz, ?_⟩
        simpa only [px, hdecode] using he
    rw [hstage px.1 (x.1, (px.2, x.2.2.2))
      (y.1, (py.2, y.2.2.2)) (z.1, (pz.2, z.2.2.2)) hold.2.2]
    simp only [hguard,
      MatrixCoordinates.product_tensor, Tensor.product, mul_ite, mul_zero]
  · have hnext : ¬ (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        eligible id x.2.1 x.1 y.1 z.1) := by
      rintro ⟨hxy, hxz, he⟩
      apply hold
      refine ⟨congrArg (fun p => (e p).1) hxy,
        congrArg (fun p => (e p).1) hxz, ?_⟩
      rw [← hdecode x.2.1] at he
      obtain ⟨word, hw, _⟩ :=
        (eligible_appendCode_iff px.1 px.2 x.1 y.1 z.1).mp he
      exact ⟨word, hw⟩
    rw [ite_eq_right hold, ite_eq_right hnext, zero_mul]

def extendBundle [Fintype NX] [Fintype NY] [Fintype NZ]
    (S : Stage B.execution (Fin (stageRefinementCount counts curveLabels n t))
      NX NY NZ BX BY BZ)
    (shape : MatrixCoordinates NX NY NZ) (hpositive : shape.Positive)
    (hvolume : shape.volume = stageRefinementCount counts curveLabels n t)
    (hrank : S.rankBound = stageCost counts curveLabels n t)
    (hrows : shape.rows = if readerPair n = .xz then
      stageRefinementCount counts curveLabels n t else 1)
    (hinner : shape.inner = if readerPair n = .xy then
      stageRefinementCount counts curveLabels n t else 1)
    (hcolumns : shape.columns = if readerPair n = .yz then
      stageRefinementCount counts curveLabels n t else 1)
    (hstage : ∀ p x y z, eligible id p x.1 y.1 z.1 →
      S.value p x y z = if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible id (appendCode p x.2.1) x.1 y.1 z.1
        then shape.tensor x.2.2 y.2.2 z.2.2 else 0) : Bundle counts t (n + 1) where
  PX := B.PX × NX
  PY := B.PY × NY
  PZ := B.PZ × NZ
  AX := B.AX × BX
  AY := B.AY × BY
  AZ := B.AZ × BZ
  execution := refinedExecution B S
  shape := B.shape.product shape
  shape_positive := B.shape.product_positive shape B.shape_positive hpositive
  normal := refinedExecution_normal B S shape hstage
  rank_exact := by
    simp only [refinedExecution, Execution.reindexOutput_rankBound,
      Execution.step_rankBound, B.rank_exact, hrank, stageAuxiliaryBudget_succ]
  volume_exact := by
    rw [MatrixCoordinates.product_volume, B.volume_exact, hvolume, stagePairingProduct_succ]
  rows_exact := by
    change B.shape.rows * shape.rows = _
    rw [B.rows_exact, hrows, pairingProduct_succ]
  inner_exact := by
    change B.shape.inner * shape.inner = _
    rw [B.inner_exact, hinner, pairingProduct_succ]
  columns_exact := by
    change B.shape.columns * shape.columns = _
    rw [B.columns_exact, hcolumns, pairingProduct_succ]
  pairing_budget := by
    change (B.shape.product shape).volume ≤ B.execution.rankBound * S.rankBound
    rw [MatrixCoordinates.product_volume]
    apply Nat.mul_le_mul B.pairing_budget
    rw [hvolume, hrank]
    exact LabelHierarchySeparation.population_le_poolAuxiliaryCost _

end Successor

section ConcreteStages

variable {counts : Scalar → ℕ} {t n : ℕ}

def extendXY (B : Bundle counts t n) (hn : n < 5)
    (hfirst : curveFirstSide n = .x) (hsecond : curveSecondSide n = .y) :
    Bundle counts t (n + 1) := Classical.choice (by
  have hpair : readerPair n = .xy := by
    interval_cases n <;> simp_all [curveFirstSide, curveSecondSide, readerPair]
  have hagree : ∀ (p : Prefix counts t n) (x y z : Coordinate counts t), eligible id p x y z →
      firstRead id p x = secondRead id p y := by
    intro p x y z he
    simpa only [hfirst, hsecond, coordinateOf] using
      readable_of_eligible id p x y z hn he
  obtain ⟨S, _, hrank, _, _, _, _, hvalue⟩ :=
    ConditionalHierarchyStage.exists_actualPoolStage counts curveLabels n t B.execution id
      (firstRead id) (secondRead id) (eligible id) (previous_eligible B) hagree
  refine ⟨extendBundle B S (GeometricStageCoordinates.xy _)
    (GeometricStageCoordinates.xy_positive (stageRefinementCount_pos counts curveLabels n t))
    (GeometricStageCoordinates.xy_volume _) hrank
    (by simp [hpair, GeometricStageCoordinates.xy])
    (by simp [hpair, GeometricStageCoordinates.xy])
    (by simp [hpair, GeometricStageCoordinates.xy]) ?_⟩
  intro p x y z he
  rw [hvalue]
  obtain ⟨word, hw⟩ := he
  exact CW75ReorderedGeometricValues.raw_XY_normal p hn hfirst hsecond x y z word hw)

def extendXZ (B : Bundle counts t n) (hn : n < 5)
    (hfirst : curveFirstSide n = .x) (hsecond : curveSecondSide n = .z) :
    Bundle counts t (n + 1) := Classical.choice (by
  have hpair : readerPair n = .xz := by
    interval_cases n <;> simp_all [curveFirstSide, curveSecondSide, readerPair]
  have hagree : ∀ (p : Prefix counts t n) (x y z : Coordinate counts t), eligible id p x y z →
      firstRead id p x = secondRead id p z := by
    intro p x y z he
    simpa only [hfirst, hsecond, coordinateOf] using
      readable_of_eligible id p x y z hn he
  obtain ⟨S, _, hrank, _, _, _, _, hvalue⟩ :=
    OrientedConditionalHierarchyStage.exists_actualPoolStage_XZ counts curveLabels n t B.execution id
      (firstRead id) (secondRead id) (eligible id) (previous_eligible B) hagree
  refine ⟨extendBundle B S (GeometricStageCoordinates.xz _)
    (GeometricStageCoordinates.xz_positive (stageRefinementCount_pos counts curveLabels n t))
    (GeometricStageCoordinates.xz_volume _) hrank
    (by simp [hpair, GeometricStageCoordinates.xz])
    (by simp [hpair, GeometricStageCoordinates.xz])
    (by simp [hpair, GeometricStageCoordinates.xz]) ?_⟩
  intro p x y z he
  rw [hvalue]
  obtain ⟨word, hw⟩ := he
  exact CW75ReorderedGeometricValues.raw_XZ_normal p hn hfirst hsecond x y z word hw)

def extendYZ (B : Bundle counts t n) (hn : n < 5)
    (hfirst : curveFirstSide n = .y) (hsecond : curveSecondSide n = .z) :
    Bundle counts t (n + 1) := Classical.choice (by
  have hpair : readerPair n = .yz := by
    interval_cases n <;> simp_all [curveFirstSide, curveSecondSide, readerPair]
  have hagree : ∀ (p : Prefix counts t n) (x y z : Coordinate counts t), eligible id p x y z →
      firstRead id p y = secondRead id p z := by
    intro p x y z he
    simpa only [hfirst, hsecond, coordinateOf] using
      readable_of_eligible id p x y z hn he
  obtain ⟨S, _, hrank, _, _, _, _, hvalue⟩ :=
    OrientedConditionalHierarchyStage.exists_actualPoolStage_YZ counts curveLabels n t B.execution id
      (firstRead id) (secondRead id) (eligible id) (previous_eligible B) hagree
  refine ⟨extendBundle B S (GeometricStageCoordinates.yz _)
    (GeometricStageCoordinates.yz_positive (stageRefinementCount_pos counts curveLabels n t))
    (GeometricStageCoordinates.yz_volume _) hrank
    (by simp [hpair, GeometricStageCoordinates.yz])
    (by simp [hpair, GeometricStageCoordinates.yz])
    (by simp [hpair, GeometricStageCoordinates.yz]) ?_⟩
  intro p x y z he
  rw [hvalue]
  obtain ⟨word, hw⟩ := he
  exact CW75ReorderedGeometricValues.raw_YZ_normal p hn hfirst hsecond x y z word hw)

end ConcreteStages

def realize (counts : Scalar → ℕ) (t : ℕ) : Bundle counts t 5 :=
  let B0 := initial counts t
  let B1 : Bundle counts t 1 := extendXY B0 (by decide) rfl rfl
  let B2 : Bundle counts t 2 := extendXZ B1 (by decide) rfl rfl
  let B3 : Bundle counts t 3 := extendXY B2 (by decide) rfl rfl
  let B4 : Bundle counts t 4 := extendYZ B3 (by decide) rfl rfl
  extendYZ B4 (by decide) rfl rfl

theorem realize_dimensions (counts : Scalar → ℕ) (t : ℕ) :
    (realize counts t).shape.rows =
        ConditionalLabels.stagePairingSize counts curveLabels 5 curveReaderPair .xz t ∧
    (realize counts t).shape.inner =
        ConditionalLabels.stagePairingSize counts curveLabels 5 curveReaderPair .xy t ∧
    (realize counts t).shape.columns =
        ConditionalLabels.stagePairingSize counts curveLabels 5 curveReaderPair .yz t := by
  have h (pair : ReaderPair) : pairingProduct counts t pair 5 =
      ConditionalLabels.stagePairingSize counts curveLabels 5 curveReaderPair pair t := by
    change (∏ i ∈ Finset.range 5,
      if readerPair i = pair then stageRefinementCount counts curveLabels i t else 1) =
      ∏ i : Fin 5,
        if readerPair i.val = pair then stageRefinementCount counts curveLabels i.val t else 1
    exact (Fin.prod_univ_eq_prod_range
      (fun i => if readerPair i = pair then
        stageRefinementCount counts curveLabels i t else 1) 5).symm
  exact ⟨(realize counts t).rows_exact.trans (h .xz),
    (realize counts t).inner_exact.trans (h .xy),
    (realize counts t).columns_exact.trans (h .yz)⟩

theorem realize_rankBound (counts : Scalar → ℕ) (t : ℕ) :
    (realize counts t).execution.rankBound = stageAuxiliaryBudget counts curveLabels 5 t :=
  (realize counts t).rank_exact

theorem realize_volume (counts : Scalar → ℕ) (t : ℕ) :
    (realize counts t).shape.volume = Fintype.card (ExactWords (fun a => t * counts a)) := by
  rw [(realize counts t).volume_exact]
  simpa only [exactWords_card] using
    (stagePairingProduct_eq_exactWords_card counts curveLabels 5 curve_completeRecord_injective t)

theorem realize_pairing_budget (counts : Scalar → ℕ) (t : ℕ) :
    (realize counts t).shape.volume ≤ (realize counts t).execution.rankBound :=
  (realize counts t).pairing_budget

theorem realize_value (counts : Scalar → ℕ) (t : ℕ)
    (x : Coordinate counts t × (Prefix counts t 5 × (realize counts t).PX))
    (y : Coordinate counts t × (Prefix counts t 5 × (realize counts t).PY))
    (z : Coordinate counts t × (Prefix counts t 5 × (realize counts t).PZ)) :
    (realize counts t).execution.value x y z =
      if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        x.1 = longX (terminalWord x.2.1).val ∧
        y.1 = longY (terminalWord x.2.1).val ∧
        z.1 = longZ (terminalWord x.2.1).val
      then (realize counts t).shape.tensor x.2.2 y.2.2 z.2.2 else 0 := by
  rw [(realize counts t).normal]
  simp only [prefixValue, terminal_eligible_iff]

theorem realize_label_card (counts : Scalar → ℕ) (t : ℕ) :
    Fintype.card (Prefix counts t 5) = Fintype.card (ExactWords (fun a => t * counts a)) := by
  rw [exactWords_card]
  let : DecidableEq Scalar := Classical.decEq Scalar
  calc
    Fintype.card (Prefix counts t 5) =
        Fintype.card (PopulationWords (Position counts t) (fun a => t * counts a)) :=
      Fintype.card_congr
        (sourcePrefixEquiv counts curveLabels 5 t (Position counts t) curve_completeRecord_injective)
    _ = Nat.multinomial Finset.univ (fun a => t * counts a) :=
      populationWords_card (I := Position counts t)
        (fun a => t * counts a) (position_card counts t)

end MatrixMultiplication.CW75ReorderedExecution

end

end OAI
