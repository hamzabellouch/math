import OAI.LinearAlgebra.MatrixMultiplication.Completion.HierarchyWords
import OAI.LinearAlgebra.MatrixMultiplication.Completion.GeometricValues
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexConditionalHierarchyStage
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexOrientedConditionalHierarchyStage
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexGeometricStageCoordinates
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialExecutionReindex

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionExecution

open MatrixMultiplication.Foundation CompletionHierarchyWords ConditionalPrefixWords
open PolynomialKernelExecution ExecutionPairingBudget StageHierarchyResources
open scoped BigOperators Classical

variable {A X Y Z : Type} [Fintype A]
variable (H : ReadableHierarchy A X Y Z)

abbrev Position (counts : A → ℕ) (t : ℕ) := Fin (t * ∑ a, counts a)
abbrev Coordinate (U : Type) (counts : A → ℕ) (t : ℕ) := Position counts t → U
abbrev Prefix (counts : A → ℕ) (t n : ℕ) :=
  ExactPrefix counts H.labels n t (Position counts t)

def support (counts : A → ℕ) (t : ℕ)
    (x : Coordinate X counts t) (y : Coordinate Y counts t)
    (z : Coordinate Z counts t) : Prop :=
  ∀ i, ∃ a : A, H.x a = x i ∧ H.y a = y i ∧ H.z a = z i

def pairingProduct (counts : A → ℕ) (t : ℕ) (pair : ReaderPair) (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, if H.pair i = pair then
    stageRefinementCount counts H.labels i t else 1

@[simp] theorem pairingProduct_zero (counts : A → ℕ) (t : ℕ) (pair : ReaderPair) :
    pairingProduct H counts t pair 0 = 1 := by simp [pairingProduct]

theorem pairingProduct_succ (counts : A → ℕ) (t : ℕ) (pair : ReaderPair) (n : ℕ) :
    pairingProduct H counts t pair (n + 1) = pairingProduct H counts t pair n *
      (if H.pair n = pair then stageRefinementCount counts H.labels n t else 1) := by
  simp only [pairingProduct, Finset.prod_range_succ]

def prefixValue {PX PY PZ : Type*} (counts : A → ℕ) (t n : ℕ)
    (pairing : Tensor ℂ PX PY PZ) :
    Tensor ℂ (Coordinate X counts t × (Prefix H counts t n × PX))
      (Coordinate Y counts t × (Prefix H counts t n × PY))
      (Coordinate Z counts t × (Prefix H counts t n × PZ)) :=
  fun x y z => if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
      eligible H id x.2.1 x.1 y.1 z.1 then pairing x.2.2 y.2.2 z.2.2 else 0

structure Bundle (counts : A → ℕ) (t n : ℕ) where
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
  execution : Execution (Coordinate X counts t) (Coordinate Y counts t) (Coordinate Z counts t)
    (Prefix H counts t n) PX PY PZ AX AY AZ
      (support H counts t)
  shape : MatrixCoordinates PX PY PZ
  shape_positive : shape.Positive
  normal : execution.value = prefixValue H counts t n shape.tensor
  rank_exact : execution.rankBound = stageAuxiliaryBudget counts H.labels n t
  volume_exact : shape.volume = stagePairingProduct counts H.labels n t
  rows_exact : shape.rows = pairingProduct H counts t .xz n
  inner_exact : shape.inner = pairingProduct H counts t .xy n
  columns_exact : shape.columns = pairingProduct H counts t .yz n
  pairing_budget : shape.volume ≤ execution.rankBound

attribute [instance] Bundle.finitePX Bundle.finitePY Bundle.finitePZ
attribute [instance] Bundle.finiteAX Bundle.finiteAY Bundle.finiteAZ

theorem position_card (counts : A → ℕ) (t : ℕ) :
    Fintype.card (Position counts t) = ∑ a, t * counts a := by
  simp [Position, Finset.mul_sum]

def scalarAuxiliary : Tensor ℂ PUnit PUnit PUnit := fun _ _ _ => 1

theorem scalarAuxiliary_rank : Tensor.RankAtMost scalarAuxiliary 1 := by
  refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, ?_⟩
  funext x y z
  simp [scalarAuxiliary, Tensor.rankOne]

def initial (counts : A → ℕ) (t : ℕ) : Bundle H counts t 0 := by
  let E : Execution (Coordinate X counts t) (Coordinate Y counts t)
      (Coordinate Z counts t) (Prefix H counts t 0) PUnit PUnit PUnit
      PUnit PUnit PUnit (support H counts t) := {
    auxiliary := scalarAuxiliary
    rankBound := 1
    auxiliary_rank := scalarAuxiliary_rank
    order := 0
    leftDegree := 0
    middleDegree := 0
    rightDegree := 0
    leftMap := fun _ _ _ => 1
    middleMap := fun _ _ _ => 1
    rightMap := fun _ _ _ => 1
    left_degree := by intros; simp
    middle_degree := by intros; simp
    right_degree := by intros; simp
    value := prefixValue H counts t 0 MatrixCoordinates.scalar.tensor
    vanishes := by intro _ _ _ _ j hj; omega
    leading := by
      intro x y z hs
      have hxy : x.2.1 = y.2.1 := Subsingleton.elim _ _
      have hxz : x.2.1 = z.2.1 := Subsingleton.elim _ _
      have he : eligible H id x.2.1 x.1 y.1 z.1 :=
        (root_eligible_iff H x.2.1 x.1 y.1 z.1).mpr hs
      change _ = (if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        eligible H id x.2.1 x.1 y.1 z.1 then
          MatrixCoordinates.scalar.tensor x.2.2 y.2.2 z.2.2 else 0)
      rw [ite_eq_left ⟨hxy, hxz, he⟩, MatrixCoordinates.scalar_tensor]
      simp [PolynomialLocalConstruction.kernel, LocalMaps.fiberTransform, scalarAuxiliary]
    synchronized := by intro _ _ _ _ _; exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  }
  exact {
    PX := PUnit
    PY := PUnit
    PZ := PUnit
    AX := PUnit
    AY := PUnit
    AZ := PUnit
    execution := E
    shape := MatrixCoordinates.scalar
    shape_positive := MatrixCoordinates.scalar_positive
    normal := rfl
    rank_exact := by simp [E, stageAuxiliaryBudget]
    volume_exact := by simp [stagePairingProduct]
    rows_exact := by simp [MatrixCoordinates.scalar]
    inner_exact := by simp [MatrixCoordinates.scalar]
    columns_exact := by simp [MatrixCoordinates.scalar]
    pairing_budget := le_rfl
  }

variable {H}

theorem previous_eligible {counts : A → ℕ} {t n : ℕ} (B : Bundle H counts t n)
    (x : Coordinate X counts t × (Prefix H counts t n × B.PX))
    (y : Coordinate Y counts t × (Prefix H counts t n × B.PY))
    (z : Coordinate Z counts t × (Prefix H counts t n × B.PZ))
    (_hs : support H counts t x.1 y.1 z.1)
    (hn : B.execution.value x y z ≠ 0) : eligible H id x.2.1 x.1 y.1 z.1 := by
  rw [B.normal] at hn
  by_contra h
  exact hn (by simp [prefixValue, h])

section Successor

variable {counts : A → ℕ} {t n : ℕ} (B : Bundle H counts t n)
variable {NX NY NZ BX BY BZ : Type}
variable [Fintype BX] [Fintype BY] [Fintype BZ]

def refinedExecution
    (S : Stage B.execution (Fin (stageRefinementCount counts H.labels n t))
      NX NY NZ BX BY BZ) :
    Execution (Coordinate X counts t) (Coordinate Y counts t) (Coordinate Z counts t)
      (Prefix H counts t (n + 1)) (B.PX × NX) (B.PY × NY) (B.PZ × NZ)
      (B.AX × BX) (B.AY × BY) (B.AZ × BZ)
      (support H counts t) :=
  (B.execution.step S).reindexOutput
    (nextPrefixEquiv counts H.labels n t (Position counts t))
    (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)

theorem refinedExecution_normal
    (S : Stage B.execution (Fin (stageRefinementCount counts H.labels n t))
      NX NY NZ BX BY BZ)
    (shape : MatrixCoordinates NX NY NZ)
    (hstage : ∀ p x y z, eligible H id p x.1 y.1 z.1 →
      S.value p x y z = if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible H id (appendCode p x.2.1) x.1 y.1 z.1
        then shape.tensor x.2.2 y.2.2 z.2.2 else 0) :
    (refinedExecution B S).value =
      prefixValue H counts t (n + 1) (B.shape.product shape).tensor := by
  classical
  funext x y z
  let e := nextPrefixEquiv counts H.labels n t (Position counts t)
  let px := e x.2.1
  let py := e y.2.1
  let pz := e z.2.1
  have hdecode (p : Prefix H counts t (n + 1)) :
      appendCode (e p).1 (e p).2 = p := e.symm_apply_apply p
  change B.execution.value (x.1, (px.1, x.2.2.1))
      (y.1, (py.1, y.2.2.1)) (z.1, (pz.1, z.2.2.1)) *
    S.value px.1 (x.1, (px.2, x.2.2.2))
      (y.1, (py.2, y.2.2.2)) (z.1, (pz.2, z.2.2.2)) = _
  rw [B.normal]
  simp only [prefixValue]
  by_cases hold : px.1 = py.1 ∧ px.1 = pz.1 ∧ eligible H id px.1 x.1 y.1 z.1
  · rw [ite_eq_left hold]
    have hguard :
        (px.2 = py.2 ∧ px.2 = pz.2 ∧ eligible H id (appendCode px.1 px.2) x.1 y.1 z.1) ↔
        (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧ eligible H id x.2.1 x.1 y.1 z.1) := by
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
        eligible H id x.2.1 x.1 y.1 z.1) := by
      rintro ⟨hxy, hxz, he⟩
      apply hold
      refine ⟨congrArg (fun p => (e p).1) hxy,
        congrArg (fun p => (e p).1) hxz, ?_⟩
      rw [← hdecode x.2.1] at he
      obtain ⟨word, hw, _⟩ :=
        (eligible_appendCode_iff H px.1 px.2 x.1 y.1 z.1).mp he
      exact ⟨word, hw⟩
    rw [ite_eq_right hold, ite_eq_right hnext, zero_mul]

def extendBundle [Fintype NX] [Fintype NY] [Fintype NZ]
    (S : Stage B.execution (Fin (stageRefinementCount counts H.labels n t))
      NX NY NZ BX BY BZ)
    (shape : MatrixCoordinates NX NY NZ) (hpositive : shape.Positive)
    (hvolume : shape.volume = stageRefinementCount counts H.labels n t)
    (hrank : S.rankBound = stageCost counts H.labels n t)
    (hrows : shape.rows = if H.pair n = .xz then
      stageRefinementCount counts H.labels n t else 1)
    (hinner : shape.inner = if H.pair n = .xy then
      stageRefinementCount counts H.labels n t else 1)
    (hcolumns : shape.columns = if H.pair n = .yz then
      stageRefinementCount counts H.labels n t else 1)
    (hstage : ∀ p x y z, eligible H id p x.1 y.1 z.1 →
      S.value p x y z = if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible H id (appendCode p x.2.1) x.1 y.1 z.1
        then shape.tensor x.2.2 y.2.2 z.2.2 else 0) : Bundle H counts t (n + 1) where
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
    change B.execution.rankBound * S.rankBound = _
    rw [B.rank_exact, hrank, stageAuxiliaryBudget_succ]
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

variable {counts : A → ℕ} {t n : ℕ}

def extendXY (B : Bundle H counts t n) (hn : n < H.depth)
    (hpair : H.pair n = .xy) : Bundle H counts t (n + 1) := Classical.choice (by
  have hagree : ∀ (p : Prefix H counts t n)
      (x : Coordinate X counts t) (y : Coordinate Y counts t)
      (z : Coordinate Z counts t), eligible H id p x y z →
      readXYX H id hpair p x = readXYY H id hpair p y := by
    intro p x y z he
    exact readable_XY H id hpair p x y z hn he
  obtain ⟨S, _, hrank, _, _, _, _, hvalue⟩ :=
    ConditionalHierarchyStage.exists_actualPoolStage counts H.labels n t B.execution id
      (readXYX H id hpair) (readXYY H id hpair)
      (eligible H id) (previous_eligible B) hagree
  refine ⟨extendBundle B S (GeometricStageCoordinates.xy _)
    (GeometricStageCoordinates.xy_positive (stageRefinementCount_pos counts H.labels n t))
    (GeometricStageCoordinates.xy_volume _) hrank
    (by simp [hpair, GeometricStageCoordinates.xy])
    (by simp [hpair, GeometricStageCoordinates.xy])
    (by simp [hpair, GeometricStageCoordinates.xy]) ?_⟩
  intro p x y z he
  rw [hvalue]
  obtain ⟨word, hw⟩ := he
  exact CompletionGeometricValues.raw_XY_normal H p hn hpair x y z word hw)

def extendXZ (B : Bundle H counts t n) (hn : n < H.depth)
    (hpair : H.pair n = .xz) : Bundle H counts t (n + 1) := Classical.choice (by
  have hagree : ∀ (p : Prefix H counts t n)
      (x : Coordinate X counts t) (y : Coordinate Y counts t)
      (z : Coordinate Z counts t), eligible H id p x y z →
      readXZX H id hpair p x = readXZZ H id hpair p z := by
    intro p x y z he
    exact readable_XZ H id hpair p x y z hn he
  obtain ⟨S, _, hrank, _, _, _, _, hvalue⟩ :=
    OrientedConditionalHierarchyStage.exists_actualPoolStage_XZ counts H.labels n t B.execution id
      (readXZX H id hpair) (readXZZ H id hpair)
      (eligible H id) (previous_eligible B) hagree
  refine ⟨extendBundle B S (GeometricStageCoordinates.xz _)
    (GeometricStageCoordinates.xz_positive (stageRefinementCount_pos counts H.labels n t))
    (GeometricStageCoordinates.xz_volume _) hrank
    (by simp [hpair, GeometricStageCoordinates.xz])
    (by simp [hpair, GeometricStageCoordinates.xz])
    (by simp [hpair, GeometricStageCoordinates.xz]) ?_⟩
  intro p x y z he
  rw [hvalue]
  obtain ⟨word, hw⟩ := he
  exact CompletionGeometricValues.raw_XZ_normal H p hn hpair x y z word hw)

def extendYZ (B : Bundle H counts t n) (hn : n < H.depth)
    (hpair : H.pair n = .yz) : Bundle H counts t (n + 1) := Classical.choice (by
  have hagree : ∀ (p : Prefix H counts t n)
      (x : Coordinate X counts t) (y : Coordinate Y counts t)
      (z : Coordinate Z counts t), eligible H id p x y z →
      readYZY H id hpair p y = readYZZ H id hpair p z := by
    intro p x y z he
    exact readable_YZ H id hpair p x y z hn he
  obtain ⟨S, _, hrank, _, _, _, _, hvalue⟩ :=
    OrientedConditionalHierarchyStage.exists_actualPoolStage_YZ counts H.labels n t B.execution id
      (readYZY H id hpair) (readYZZ H id hpair)
      (eligible H id) (previous_eligible B) hagree
  refine ⟨extendBundle B S (GeometricStageCoordinates.yz _)
    (GeometricStageCoordinates.yz_positive (stageRefinementCount_pos counts H.labels n t))
    (GeometricStageCoordinates.yz_volume _) hrank
    (by simp [hpair, GeometricStageCoordinates.yz])
    (by simp [hpair, GeometricStageCoordinates.yz])
    (by simp [hpair, GeometricStageCoordinates.yz]) ?_⟩
  intro p x y z he
  rw [hvalue]
  obtain ⟨word, hw⟩ := he
  exact CompletionGeometricValues.raw_YZ_normal H p hn hpair x y z word hw)

def extend (B : Bundle H counts t n) (hn : n < H.depth) :
    Bundle H counts t (n + 1) :=
  match hp : H.pair n with
  | .xy => extendXY B hn hp
  | .xz => extendXZ B hn hp
  | .yz => extendYZ B hn hp

end ConcreteStages

variable (H)

def run (counts : A → ℕ) (t : ℕ) : (n : ℕ) → n ≤ H.depth → Bundle H counts t n
  | 0, _ => initial H counts t
  | n + 1, hn => extend (run counts t n (by omega)) (by omega)

def realize (counts : A → ℕ) (t : ℕ) : Bundle H counts t H.depth :=
  run H counts t H.depth le_rfl

theorem realize_dimensions (counts : A → ℕ) (t : ℕ) :
    (realize H counts t).shape.rows =
        ConditionalLabels.stagePairingSize counts H.labels H.depth
          (fun n => H.pair n.val) .xz t ∧
    (realize H counts t).shape.inner =
        ConditionalLabels.stagePairingSize counts H.labels H.depth
          (fun n => H.pair n.val) .xy t ∧
    (realize H counts t).shape.columns =
        ConditionalLabels.stagePairingSize counts H.labels H.depth
          (fun n => H.pair n.val) .yz t := by
  have h (pair : ReaderPair) : pairingProduct H counts t pair H.depth =
      ConditionalLabels.stagePairingSize counts H.labels H.depth
        (fun n => H.pair n.val) pair t := by
    simp only [pairingProduct, ConditionalLabels.stagePairingSize,
      ConditionalLabels.pairingSize, ← Fin.prod_univ_eq_prod_range]
  exact ⟨(realize H counts t).rows_exact.trans (h .xz),
    (realize H counts t).inner_exact.trans (h .xy),
    (realize H counts t).columns_exact.trans (h .yz)⟩

theorem realize_rankBound (counts : A → ℕ) (t : ℕ) :
    (realize H counts t).execution.rankBound =
      stageAuxiliaryBudget counts H.labels H.depth t :=
  (realize H counts t).rank_exact

theorem realize_volume (counts : A → ℕ) (t : ℕ)
    (complete : Function.Injective (labelRecordOf H.labels H.depth)) :
    (realize H counts t).shape.volume =
      Fintype.card (ExactWords (fun a => t * counts a)) := by
  rw [(realize H counts t).volume_exact]
  exact stagePairingProduct_eq_exactWords_card counts H.labels H.depth complete t

theorem realize_label_card (counts : A → ℕ) (t : ℕ)
    (complete : Function.Injective (labelRecordOf H.labels H.depth)) :
    Fintype.card (Prefix H counts t H.depth) =
      Fintype.card (ExactWords (fun a => t * counts a)) := by
  rw [exactWords_card]
  calc
    Fintype.card (Prefix H counts t H.depth) =
        Fintype.card (PopulationWords (Position counts t) (fun a => t * counts a)) :=
      Fintype.card_congr
        (sourcePrefixEquiv counts H.labels H.depth t (Position counts t) complete)
    _ = Nat.multinomial Finset.univ (fun a => t * counts a) :=
      populationWords_card (I := Position counts t)
        (fun a => t * counts a) (position_card counts t)

end MatrixMultiplication.CompletionExecution

end

end OAI
