import Mathlib
import OAI.Computability.MinUncut.Machines.Relations
import OAI.Computability.MinUncut.Machines.AlphabetRetraction
import OAI.Computability.MinUncut.Encoding.BinaryCoordinates

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.RawInitialTables

open Target GraphTables

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := by fin_cases i; rfl

def slotOrder : Slot ≃ Fin 3 where
  toFun
    | .first => 0
    | .second => 1
    | .third => 2
  invFun i := if i = 0 then .first else if i = 1 then .second else .third
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

def binaryOrder (n : Nat) : (Fin n → Bool) ≃ Fin (2 ^ n) where
  toFun bits := (MinUncutGames.Integration.BinaryCoordinates.pack bits).toFin
  invFun index := MinUncutGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index)
  left_inv bits := MinUncutGames.Integration.BinaryCoordinates.unpack_pack bits
  right_inv index := by
    change (MinUncutGames.Integration.BinaryCoordinates.pack
      (MinUncutGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index))).toFin = index
    rw [MinUncutGames.Integration.BinaryCoordinates.pack_unpack]

def labelOrder : AlphabetRetraction.Label64 ≃ GraphTables.Label := binaryOrder 6

def vertexOrder (F : Formula) :
    InitialGraph.Vertex F ≃ Fin (F.«variables» + F.clauses.length + 1) :=
  ((finSumFinEquiv.sumCongr unitOrder).trans finSumFinEquiv)

def eventOrder (F : Formula) : RandomEvent F ≃ Fin (F.clauses.length * 3) :=
  ((Equiv.refl (Fin F.clauses.length)).prodCongr slotOrder).trans finProdFinEquiv

def dartOrder (F : Formula) : InitialGraph.Dart F ≃ Fin (6 * F.clauses.length + 1) :=
  (((((eventOrder F).prodCongr finTwoEquiv.symm).trans finProdFinEquiv).sumCongr
    unitOrder).trans finSumFinEquiv).trans (finCongr (by omega))

def raw64 (F : Formula) : ConstraintGraph (InitialGraph.Vertex F)
    (InitialGraph.Dart F) AlphabetRetraction.Label64 :=
  AlphabetRetraction.pullback (InitialGraph.raw F) AlphabetRetraction.decode64

def table (F : Formula) : GraphTables.Table :=
  GraphTables.ofEnumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder

@[simp] theorem table_vertices (F : Formula) :
    (table F).vertices = F.«variables» + F.clauses.length + 1 := rfl

@[simp] theorem table_darts (F : Formula) : (table F).darts = 6 * F.clauses.length + 1 := rfl

theorem table_vertices_positive (F : Formula) : 0 < (table F).vertices := by
  rw [table_vertices]; omega

theorem table_darts_positive (F : Formula) : 0 < (table F).darts := by
  rw [table_darts]; omega

theorem raw64_satisfiable_iff (F : Formula) : (raw64 F).Satisfiable ↔ F.Satisfiable :=
  (AlphabetRetraction.satisfiable_pullback_iff (InitialGraph.raw F)
    AlphabetRetraction.decode64 AlphabetRetraction.encode64
      AlphabetRetraction.decode_encode64).trans (InitialGraph.raw_satisfiable_iff F)

theorem table_semantics (F : Formula) :
    GraphTables.semantics (table F) =
      (raw64 F).reindex (vertexOrder F) (dartOrder F) labelOrder := by
  change GraphTables.semantics (GraphTables.ofGraph
    (GraphTables.enumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder)) = _
  rw [GraphTables.semantics_ofGraph]
  rfl

theorem table_satisfiable_iff (F : Formula) :
    (GraphTables.semantics (table F)).Satisfiable ↔ F.Satisfiable := by
  rw [table_semantics]
  exact ((raw64 F).satisfiable_reindex (vertexOrder F) (dartOrder F) labelOrder).trans
    (raw64_satisfiable_iff F)

theorem initial_rejection (F : Formula) (unsat : ¬ F.Satisfiable)
    (labeling : Fin (table F).vertices → GraphTables.Label) :
    1 ≤ (GraphTables.semantics (table F)).rejectionCount labeling :=
  ConstraintGraph.rejectionCount_positive _
    (fun h => unsat ((table_satisfiable_iff F).mp h)) labeling

theorem initial_size (F : Formula) :
    (table F).vertices + (table F).darts = F.«variables» + 7 * F.clauses.length + 2 := by
  rw [table_vertices, table_darts]
  omega

end MinUncutGames.Foundations.PCP.RawInitialTables

end
section
noncomputable section

namespace MinUncutGames.Foundations.PCP.FiniteGraph

structure Bundle (A : Type) where
  Vertex : Type
  Dart : Type
  vertexFintype : Fintype Vertex
  dartFintype : Fintype Dart
  vertexDecidableEq : DecidableEq Vertex
  dartDecidableEq : DecidableEq Dart
  dartNonempty : Nonempty Dart
  graph : ConstraintGraph Vertex Dart A

namespace Bundle

variable {A : Type}

instance instFintypeVertex (G : Bundle A) : Fintype G.Vertex := G.vertexFintype
instance instFintypeDart (G : Bundle A) : Fintype G.Dart := G.dartFintype
instance instDecidableEqVertex (G : Bundle A) : DecidableEq G.Vertex := G.vertexDecidableEq
instance instDecidableEqDart (G : Bundle A) : DecidableEq G.Dart := G.dartDecidableEq
instance instNonemptyDart (G : Bundle A) : Nonempty G.Dart := G.dartNonempty

instance instNonemptyVertex (G : Bundle A) : Nonempty G.Vertex := by
  obtain ⟨d⟩ := G.dartNonempty
  exact ⟨G.graph.tail d⟩

def ofGraph {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E]
    (G : ConstraintGraph V E A) : Bundle A where
  Vertex := V
  Dart := E
  vertexFintype := inferInstance
  dartFintype := inferInstance
  vertexDecidableEq := inferInstance
  dartDecidableEq := inferInstance
  dartNonempty := inferInstance
  graph := G

def size (G : Bundle A) : Nat := Fintype.card G.Vertex + Fintype.card G.Dart

def Satisfiable (G : Bundle A) : Prop := G.graph.Satisfiable

def rejectionCount (G : Bundle A) (labeling : G.Vertex → A) : Nat :=
  G.graph.rejectionCount labeling

theorem size_positive (G : Bundle A) : 0 < G.size :=
  lt_of_lt_of_le (Fintype.card_pos : 0 < Fintype.card G.Dart) (Nat.le_add_left _ _)

theorem dartCard_le_size (G : Bundle A) : Fintype.card G.Dart ≤ G.size :=
  Nat.le_add_left _ _

@[simp] theorem ofGraph_graph {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).graph = G := rfl

@[simp] theorem ofGraph_size {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).size = Fintype.card V + Fintype.card E := rfl

@[simp] theorem ofGraph_satisfiable {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).Satisfiable ↔ G.Satisfiable := Iff.rfl

@[simp] theorem ofGraph_rejectionCount {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E]
    (G : ConstraintGraph V E A) (labeling : V → A) :
    (ofGraph G).rejectionCount labeling = G.rejectionCount labeling := rfl

section Gap

variable [Fintype A] [Nonempty A]

def minimumRejections (G : Bundle A) : Nat := G.graph.minimumRejections

def gap (G : Bundle A) : ℝ := G.graph.gap

theorem exists_minimizer (G : Bundle A) :
    ∃ labeling : G.Vertex → A, G.rejectionCount labeling = G.minimumRejections :=
  G.graph.exists_minimizer

theorem gap_nonnegative (G : Bundle A) : 0 ≤ G.gap := G.graph.gap_nonnegative

theorem gap_le_one (G : Bundle A) : G.gap ≤ 1 := G.graph.gap_le_one

theorem gap_eq_zero_iff (G : Bundle A) : G.gap = 0 ↔ G.Satisfiable :=
  G.graph.gap_eq_zero_iff

theorem le_gap_iff (G : Bundle A) (ε : ℝ) :
    ε ≤ G.gap ↔ ∀ labeling : G.Vertex → A,
      ε * Fintype.card G.Dart ≤ (G.rejectionCount labeling : ℝ) :=
  G.graph.le_gap_iff ε

theorem inverse_card_le_gap_of_unsatisfiable (G : Bundle A) (unsat : ¬ G.Satisfiable) :
    1 / (Fintype.card G.Dart : ℝ) ≤ G.gap :=
  G.graph.inverse_card_le_gap_of_unsatisfiable unsat

theorem one_le_dartCard_mul_gap (G : Bundle A) (unsat : ¬ G.Satisfiable) :
    1 ≤ (Fintype.card G.Dart : ℝ) * G.gap := by
  have he : (0 : ℝ) < Fintype.card G.Dart := by exact_mod_cast Fintype.card_pos
  have h := (div_le_iff₀ he).mp (G.inverse_card_le_gap_of_unsatisfiable unsat)
  simpa only [mul_comm] using h

theorem one_le_size_mul_gap (G : Bundle A) (unsat : ¬ G.Satisfiable) :
    1 ≤ (G.size : ℝ) * G.gap := by
  have hsize : (Fintype.card G.Dart : ℝ) ≤ (G.size : ℝ) := by
    exact_mod_cast G.dartCard_le_size
  exact (G.one_le_dartCard_mul_gap unsat).trans
    (mul_le_mul_of_nonneg_right hsize G.gap_nonnegative)

@[simp] theorem ofGraph_minimumRejections {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).minimumRejections = G.minimumRejections := rfl

@[simp] theorem ofGraph_gap {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).gap = G.gap := rfl

end Gap

end Bundle

end MinUncutGames.Foundations.PCP.FiniteGraph

end
end
section
namespace MinUncutGames.Foundations.PCP.FinalConstants

def alphabet : Nat := 64
def compositionLoss : Nat := 12288
def denominator : Nat := 16 * alphabet ^ 4 * 66 * compositionLoss
def windowHalf : Nat := denominator * Preprocessing.sizeFactor
def windowSize : Nat := 2 * windowHalf + 1
def smoothingScale : Nat := 4 * alphabet * windowHalf
def endpointLength : Nat := smoothingScale ^ 2
def walkLength : Nat := 2 * endpointLength + 1

noncomputable def gain : ℝ := (windowSize : ℝ) / denominator
noncomputable def cap : ℝ := 1 / (walkLength : ℝ)

theorem denominator_positive : 0 < denominator := by
  norm_num [denominator, alphabet, compositionLoss]

theorem windowHalf_positive : 0 < windowHalf :=
  Nat.mul_pos denominator_positive Preprocessing.sizeFactor_positive

theorem walkLength_positive : 0 < walkLength := by
  simp [walkLength]

theorem gain_large : 2 * (Preprocessing.sizeFactor : ℝ) ≤ gain := by
  have hd : (0 : ℝ) < denominator := by exact_mod_cast denominator_positive
  apply (le_div_iff₀ hd).2
  simp only [windowSize, windowHalf, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  nlinarith

theorem cap_positive : 0 < cap := by
  exact one_div_pos.mpr (by exact_mod_cast walkLength_positive)

theorem cap_le_one : cap ≤ 1 := by
  apply (div_le_one (by exact_mod_cast walkLength_positive)).2
  exact_mod_cast walkLength_positive

theorem composed_gap (epsilon : ℝ) (he : 0 ≤ epsilon) :
    min (2 * epsilon) cap ≤
      gain * min (epsilon / (Preprocessing.sizeFactor : ℝ))
        (1 / (walkLength : ℝ)) := by
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have hs1 : (1 : ℝ) ≤ Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have hg : 0 ≤ gain := le_trans (by positivity) gain_large
  rw [mul_min_of_nonneg _ _ hg]
  apply min_le_min
  · calc
      2 * epsilon = (2 * (Preprocessing.sizeFactor : ℝ)) *
          (epsilon / (Preprocessing.sizeFactor : ℝ)) := by field_simp
      _ ≤ gain * (epsilon / (Preprocessing.sizeFactor : ℝ)) :=
        mul_le_mul_of_nonneg_right gain_large (div_nonneg he hs.le)
  · change cap ≤ gain * cap
    have hgain : 1 ≤ gain := by linarith [gain_large]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hgain cap_positive.le

end MinUncutGames.Foundations.PCP.FinalConstants

end
section
namespace MinUncutGames.Foundations.PCP.RoundTables

abbrev BaseTable := PreprocessingTables.BaseTable

opaque fixedWalkParameter : {n : Nat // n = 2 * FinalConstants.endpointLength} :=
  ⟨2 * FinalConstants.endpointLength, rfl⟩

def walkParameter : Nat := fixedWalkParameter.val

theorem walkParameter_eq : walkParameter = 2 * FinalConstants.endpointLength :=
  fixedWalkParameter.property

def alphabet : Nat := PoweringTables.labelCount PreprocessingTables.degree walkParameter

theorem alphabet_positive : 0 < alphabet := by
  unfold alphabet PoweringTables.labelCount
  exact Nat.pow_pos (by decide)

def powered (H : BaseTable) (table : GraphTables.Table) : GenericGraphTables.Table alphabet :=
  PoweringTables.table (PreprocessingTables.preprocess H table) walkParameter

def build (H : BaseTable) (table : GraphTables.Table) : GraphTables.Table :=
  AlphabetTable.Table.build (powered H table)

def sizeFactor : Nat := AlphabetGraphBounds.sizeFactor alphabet *
  (ExpanderFamily.growth ^ 2 * (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)))

theorem degree_positive : 0 < PreprocessingTables.degree := by
  unfold PreprocessingTables.degree
  omega

theorem dartFactor_positive (q : Nat) : 0 < AlphabetGraphBounds.dartFactor q := by
  unfold AlphabetGraphBounds.dartFactor AlphabetGraphBounds.localEventFactor
  positivity

theorem sizeFactor_positive : 0 < sizeFactor := by
  unfold sizeFactor
  apply Nat.mul_pos (AlphabetGraphBounds.sizeFactor_positive alphabet)
  apply Nat.mul_pos
  · exact Nat.pow_pos (Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one)
  · omega

theorem powered_vertices (H : BaseTable) (table : GraphTables.Table) :
    (powered H table).vertices = PreprocessingTables.vertices table := rfl

theorem powered_darts (H : BaseTable) (table : GraphTables.Table) :
    (powered H table).darts = 2 * PreprocessingTables.vertices table *
      PreprocessingTables.degree ^ (walkParameter + 1) := rfl

theorem build_darts_positive (H : BaseTable) (table : GraphTables.Table) :
    0 < (build H table).darts := by
  change 0 < (AlphabetTable.Table.build (powered H table)).darts
  rw [AlphabetTableBounds.build_darts, powered_darts]
  exact Nat.mul_pos (Nat.mul_pos
    (Nat.mul_pos (by decide) (PreprocessingTables.vertices_positive table))
    (Nat.pow_pos degree_positive)) (dartFactor_positive alphabet)

theorem build_size_le (H : BaseTable) (table : GraphTables.Table)
    (ht : 0 < table.darts) :
    (build H table).vertices + (build H table).darts ≤
      sizeFactor * (table.vertices + table.darts) := by
  have hv := PreprocessingTables.vertices_le_of_positive table ht
  have he : (powered H table).vertices + (powered H table).darts =
      PreprocessingTables.vertices table *
        (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)) := by
    rw [powered_vertices, powered_darts]
    ring
  have hp := Nat.mul_le_mul_right
    (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)) hv
  calc
    _ ≤ AlphabetGraphBounds.sizeFactor alphabet *
        ((powered H table).vertices + (powered H table).darts) :=
      AlphabetTableBounds.build_total_le (powered H table)
    _ = AlphabetGraphBounds.sizeFactor alphabet *
        (PreprocessingTables.vertices table *
          (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1))) := by rw [he]
    _ ≤ AlphabetGraphBounds.sizeFactor alphabet *
        ((ExpanderFamily.growth ^ 2 * table.darts) *
          (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1))) :=
      Nat.mul_le_mul_left _ hp
    _ = sizeFactor * table.darts := by unfold sizeFactor; ring
    _ ≤ sizeFactor * (table.vertices + table.darts) :=
      Nat.mul_le_mul_left _ (Nat.le_add_left _ _)

theorem build_completeness (H : BaseTable) (table : GraphTables.Table)
    (sat : (GraphTables.semantics table).Satisfiable) :
    (GraphTables.semantics (build H table)).Satisfiable := by
  let : Nonempty (Fin alphabet) := ⟨⟨0, alphabet_positive⟩⟩
  exact AlphabetTable.Table.perfect_completeness (powered H table)
    (PoweringTableSemantics.preserves_satisfiability
      (PreprocessingTables.preprocess H table) walkParameter
      (PreprocessingGuarantees.completeness H table sat))

abbrev Input := {table : GraphTables.Table // 0 < table.darts}

instance (input : Input) : Nonempty (Fin input.val.darts) := ⟨⟨0, input.property⟩⟩

def step (H : BaseTable) (input : Input) : Input :=
  ⟨build H input.val, build_darts_positive H input.val⟩

def initial (F : Target.Formula) : Input :=
  ⟨RawInitialTables.table F, RawInitialTables.table_darts_positive F⟩

def size (input : Input) : Nat := input.val.vertices + input.val.darts

def Satisfiable (input : Input) : Prop := (GraphTables.semantics input.val).Satisfiable

noncomputable def gap (input : Input) : ℝ := (GraphTables.semantics input.val).gap

theorem size_positive (input : Input) : 0 < size input :=
  input.property.trans_le (Nat.le_add_left _ _)

theorem gap_nonnegative (input : Input) : 0 ≤ gap input :=
  (GraphTables.semantics input.val).gap_nonnegative

theorem gap_eq_zero_iff (input : Input) : gap input = 0 ↔ Satisfiable input :=
  (GraphTables.semantics input.val).gap_eq_zero_iff

theorem one_le_size_mul_gap (input : Input) (unsat : ¬ Satisfiable input) :
    1 ≤ (size input : ℝ) * gap input := by
  have h := (GraphTables.semantics input.val).inverse_card_le_gap_of_unsatisfiable unsat
  have hp : (0 : ℝ) < input.val.darts := Nat.cast_pos.mpr input.property
  simp only [Fintype.card_fin] at h
  have hd := (div_le_iff₀ hp).mp h
  have hsize : (input.val.darts : ℝ) ≤ (size input : ℝ) := by
    exact_mod_cast (Nat.le_add_left input.val.darts input.val.vertices)
  exact (show 1 ≤ (input.val.darts : ℝ) * gap input by
    simpa only [gap, mul_comm] using hd).trans
    (mul_le_mul_of_nonneg_right hsize (gap_nonnegative input))

theorem initial_satisfiable_iff (F : Target.Formula) : Satisfiable (initial F) ↔ F.Satisfiable :=
  RawInitialTables.table_satisfiable_iff F

theorem step_completeness (H : BaseTable) (input : Input) :
    Satisfiable input → Satisfiable (step H input) := build_completeness H input.val

theorem step_size (H : BaseTable) (input : Input) :
    size (step H input) ≤ sizeFactor * size input := build_size_le H input.val input.property

end MinUncutGames.Foundations.PCP.RoundTables

end
section
namespace MinUncutGames.Foundations.PCP.AmplificationIteration

def run {X : Type*} (step : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => step (run step n x)

private theorem min_double_min (u cap : ℝ) (hc : 0 ≤ cap) :
    min (2 * min u cap) cap = min (2 * u) cap := by
  by_cases hu : u ≤ cap
  · rw [min_eq_left hu]
  · have hcu : cap ≤ u := le_of_not_ge hu
    rw [min_eq_right hcu, min_eq_right (by linarith : cap ≤ 2 * cap),
      min_eq_right (by linarith : cap ≤ 2 * u)]

theorem run_gap {X : Type*} (step : X → X) (gap : X → ℝ)
    (cap : ℝ) (hc : 0 ≤ cap)
    (amplifies : ∀ x, min (2 * gap x) cap ≤ gap (step x))
    (n : Nat) (x : X) :
    min (2 ^ n * gap x) cap ≤ gap (run step n x) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hm : min (2 * min (2 ^ n * gap x) cap) cap ≤
        min (2 * gap (run step n x)) cap :=
      min_le_min (mul_le_mul_of_nonneg_left ih (by norm_num)) le_rfl
    rw [min_double_min _ _ hc] at hm
    have h := hm.trans (amplifies (run step n x))
    simpa [run, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

theorem run_preserves {X : Type*} (step : X → X) (P : X → Prop)
    (preserves : ∀ x, P x → P (step x)) (n : Nat) (x : X) (hx : P x) :
    P (run step n x) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact preserves _ ih

theorem run_size {X : Type*} (step : X → X) (size : X → Nat) (C : Nat)
    (blowup : ∀ x, size (step x) ≤ C * size x) (n : Nat) (x : X) :
    size (run step n x) ≤ C ^ n * size x := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have h := (blowup (run step n x)).trans (Nat.mul_le_mul_left C ih)
    simpa [run, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

def rounds (n : Nat) : Nat := Nat.log2 n + 1

theorem rounds_large (n : Nat) : n < 2 ^ rounds n := by
  simpa [rounds, Nat.log2_eq_log_two] using
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n)

theorem rounds_power_le {n : Nat} (hn : 0 < n) : 2 ^ rounds n ≤ 2 * n := by
  have h := Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  simpa [rounds, Nat.log2_eq_log_two, pow_succ, Nat.mul_comm] using
    (Nat.mul_le_mul_right 2 h)

theorem blowup_rounds_le {C degree n : Nat} (hn : 0 < n) (hC : C ≤ 2 ^ degree) :
    C ^ rounds n ≤ (2 * n) ^ degree := by
  calc
    C ^ rounds n ≤ (2 ^ degree) ^ rounds n := Nat.pow_le_pow_left hC _
    _ = (2 ^ rounds n) ^ degree := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm degree (rounds n)]
    _ ≤ (2 * n) ^ degree := Nat.pow_le_pow_left (rounds_power_le hn) _

theorem run_size_polynomial {X : Type*} (step : X → X) (size : X → Nat)
    {C degree n : Nat} (hn : 0 < n) (hC : C ≤ 2 ^ degree)
    (blowup : ∀ x, size (step x) ≤ C * size x) (x : X) :
    size (run step (rounds n) x) ≤ (2 * n) ^ degree * size x :=
  (run_size step size C blowup (rounds n) x).trans
    (Nat.mul_le_mul_right _ (blowup_rounds_le hn hC))

theorem run_reaches_cap {X : Type*} (step : X → X) (gap : X → ℝ)
    (cap : ℝ) (hc : 0 ≤ cap) (hc1 : cap ≤ 1)
    (amplifies : ∀ x, min (2 * gap x) cap ≤ gap (step x))
    (n : Nat) (x : X) (hg : 0 ≤ gap x) (hstart : 1 ≤ (n : ℝ) * gap x) :
    cap ≤ gap (run step (rounds n) x) := by
  have hp : (n : ℝ) ≤ (2 : ℝ) ^ rounds n := by
    exact_mod_cast (Nat.le_of_lt (rounds_large n))
  have hcap : cap ≤ (2 : ℝ) ^ rounds n * gap x :=
    hc1.trans (hstart.trans (mul_le_mul_of_nonneg_right hp hg))
  have h := run_gap step gap cap hc amplifies (rounds n) x
  rwa [min_eq_right hcap] at h

end MinUncutGames.Foundations.PCP.AmplificationIteration

end
section
namespace MinUncutGames.Foundations.PCP.VerifierToCNF

open Target

abbrev BoolTriple := Bool × Bool × Bool

def tripleValue (t : BoolTriple) : Bool := (t.1 || t.2.1) || t.2.2

def chainView : List Bool → List Bool → List BoolTriple
  | [a, b, c], [] => [(a, b, c)]
  | a :: b :: rest, y :: ys => (a, b, y) :: chainView ((!y) :: rest) ys
  | _, _ => []

def fillBits (bits : List Bool) : List Bool :=
  match bits with
  | a :: b :: c :: d :: rest =>
      (!(a || b)) :: fillBits ((a || b) :: c :: d :: rest)
  | _ => []
termination_by bits.length
decreasing_by simp_wf

theorem chainView_length (bits ys : List Bool)
    (size : bits.length = ys.length + 3) :
    (chainView bits ys).length = ys.length + 1 := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => rfl
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have h := ih ((!y) :: rest) smaller
      simpa only [chainView, List.length_cons] using congrArg (fun n => n + 1) h

theorem chainView_sound (bits ys : List Bool)
    (size : bits.length = ys.length + 3)
    (accepted : (chainView bits ys).all tripleValue = true) : bits.any id = true := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => simpa [chainView, tripleValue, Bool.or_assoc] using accepted
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have accepted' : tripleValue (a, b, y) = true ∧
          (chainView ((!y) :: rest) ys).all tripleValue = true := by
        simpa only [chainView, List.all_cons, Bool.and_eq_true] using accepted
      have tailAccepted := ih ((!y) :: rest) smaller accepted'.2
      cases a <;> cases b <;> cases y <;> simp_all [tripleValue]

theorem fillBits_length (bits : List Bool) (size : 3 ≤ bits.length) :
    (fillBits bits).length + 3 = bits.length := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_length ((a || b) :: c :: d :: rest) (by simp)
    rw [fillBits]
    change (fillBits ((a || b) :: c :: d :: rest)).length + 1 + 3 = rest.length + 4
    simp only [List.length_cons] at ih
    omega
termination_by bits.length
decreasing_by simp_wf

theorem fillBits_correct (bits : List Bool) (size : 3 ≤ bits.length) :
    (chainView bits (fillBits bits)).all tripleValue = true ↔ bits.any id = true := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits, chainView, tripleValue, Bool.or_assoc]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_correct ((a || b) :: c :: d :: rest) (by simp)
    have tautology : tripleValue (a, b, !(a || b)) = true := by
      cases a <;> cases b <;> rfl
    rw [fillBits]
    simp only [chainView, List.all_cons, Bool.not_not]
    rw [tautology]
    simp only [Bool.true_and]
    simpa [Bool.or_assoc] using ih
termination_by bits.length
decreasing_by simp_wf

theorem zero_false_count_iff_all (bits : List Bool) :
    bits.count false = 0 ↔ bits.all id = true := by
  induction bits with
  | nil => simp
  | cons b bits ih => cases b <;> simp [ih]

theorem chainView_failed (bits ys : List Bool)
    (size : bits.length = ys.length + 3) (failed : bits.any id = false) :
    1 ≤ ((chainView bits ys).map tripleValue).count false := by
  by_contra none
  have zero : ((chainView bits ys).map tripleValue).count false = 0 := by omega
  have all := (zero_false_count_iff_all _).mp zero
  have accepted : (chainView bits ys).all tripleValue = true := by
    simpa only [List.all_map, Function.comp_def, id_eq] using all
  have impossible := chainView_sound bits ys size accepted
  rw [failed] at impossible
  contradiction

abbrev Pattern (q : Nat) := Fin q → Bool

def patterns : (q : Nat) → List (Pattern q)
  | 0 => [Fin.elim0]
  | q + 1 => (patterns q).flatMap (fun p => [Fin.cases false p, Fin.cases true p])

theorem flatMap_pair_length {α β : Type*} (xs : List α) (f g : α → β) :
    (xs.flatMap (fun x => [f x, g x])).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem patterns_length (q : Nat) : (patterns q).length = 2 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [patterns, flatMap_pair_length, ih, Nat.pow_succ]
    exact Nat.mul_comm _ _

theorem mem_patterns (q : Nat) (p : Pattern q) : p ∈ patterns q := by
  induction q with
  | zero =>
    have h : p = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [patterns, h]
  | succ q ih =>
    let tail : Pattern q := fun i => p i.succ
    have htail : tail ∈ patterns q := ih tail
    have prefixEquality : Fin.cases (p 0) tail = p := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    apply List.mem_flatMap.mpr
    refine ⟨tail, htail, ?_⟩
    cases h : p 0 with
    | false =>
      have hp : Fin.cases false tail = p := by simpa only [h] using prefixEquality
      exact List.mem_cons.mpr (Or.inl hp.symm)
    | true =>
      have hp : Fin.cases true tail = p := by simpa only [h] using prefixEquality
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hp.symm)))

abbrev PatternIndex (q : Nat) := Fin (patterns q).length
def patternAt (q : Nat) (p : PatternIndex q) : Pattern q := (patterns q)[p.val]

theorem patternAt_surjective (q : Nat) (bits : Pattern q) :
    ∃ p : PatternIndex q, patternAt q p = bits := by
  obtain ⟨i, hi, h⟩ := List.getElem_of_mem (mem_patterns q bits)
  exact ⟨⟨i, hi⟩, h⟩

structure FiniteVerifier (q : Nat) where
  «variables» : Nat
  events : Nat
  query : Fin events → Fin q → Fin «variables»
  accepts : Fin events → Pattern q → Bool

def eventValue {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) : Bool := V.accepts e (fun i => A (V.query e i))

def rejectedEventCount {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool) : Nat :=
  ((List.finRange V.events).map (eventValue V A)).count false

def auxiliaryCount {q : Nat} (V : FiniteVerifier q) : Nat :=
  V.events * (patterns q).length * (q - 3)

def outputVariables {q : Nat} (V : FiniteVerifier q) : Nat := V.«variables» + auxiliaryCount V

def oldIndex {q : Nat} (V : FiniteVerifier q) (v : Fin V.«variables») : Fin (outputVariables V) :=
  Fin.castAdd (auxiliaryCount V) v

def freshIndex {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) : Fin (outputVariables V) :=
  Fin.natAdd V.«variables» (finProdFinEquiv (finProdFinEquiv (e, p), j))

theorem freshIndex_value {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) :
    (freshIndex V e p j).val =
      V.«variables» + ((e.val * (patterns q).length + p.val) * (q - 3) + j.val) := by
  simp [freshIndex, Fin.natAdd, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

def liftLiteral {q : Nat} (V : FiniteVerifier q) (l : Literal V.«variables») :
    Literal (outputVariables V) := ⟨oldIndex V l.variableIndex, l.positive⟩

def forbiddenLiteral {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (i : Fin q) : Literal V.«variables» :=
  ⟨V.query e i, !(patternAt q p i)⟩

def forbiddenClause {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Literal (outputVariables V)) :=
  List.ofFn (fun i => liftLiteral V (forbiddenLiteral V e p i))

def auxiliaryNames {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Fin (outputVariables V)) :=
  List.ofFn (freshIndex V e p)

def splitLong {n : Nat} : List (Literal n) → List (Fin n) → List (Clause n)
  | [a, b, c], [] => [#v[a, b, c]]
  | a :: b :: rest, y :: ys =>
      #v[a, b, ⟨y, true⟩] :: splitLong (⟨y, false⟩ :: rest) ys
  | _, _ => []

def tautology {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    Clause (outputVariables V) :=
  let v := oldIndex V (V.query e ⟨0, by omega⟩)
  #v[⟨v, true⟩, ⟨v, false⟩, ⟨v, true⟩]

def block {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events)
    (p : PatternIndex q) : List (Clause (outputVariables V)) :=
  if V.accepts e (patternAt q p) then List.replicate (q - 2) (tautology V hq e)
  else splitLong (forbiddenClause V e p) (auxiliaryNames V e p)

def eventBlock {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    List (Clause (outputVariables V)) :=
  (List.finRange (patterns q).length).flatMap (block V hq e)

def convert {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) : Formula where
  «variables» := outputVariables V
  clauses := (List.finRange V.events).flatMap (eventBlock V hq)

def clauseFailures {n : Nat} (clauses : List (Clause n)) (A : Fin n → Bool) : Nat :=
  (clauses.map (fun c => c.eval A)).count false

theorem splitLong_values {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (A : Fin n → Bool) :
    (splitLong ls ys).map (fun c => c.eval A) =
      (chainView (ls.map (fun l => l.eval A)) (ys.map A)).map tripleValue := by
  induction ys generalizing ls with
  | nil =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | [_, _] => rfl
    | [a, b, c] => rfl
    | _ :: _ :: _ :: _ :: _ => rfl
  | cons y ys ih =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | a :: b :: rest =>
      have h := ih (⟨y, false⟩ :: rest)
      simp only [splitLong, List.map_cons, chainView]
      apply congrArg₂ List.cons
      · rfl
      · simpa only [List.map_cons, Literal.eval, Bool.false_eq_true, ↓reduceIte] using h

theorem splitLong_length {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (size : ls.length = ys.length + 3) : (splitLong ls ys).length = ys.length + 1 := by
  have values := congrArg List.length (splitLong_values ls ys (fun _ => false))
  simp only [List.length_map] at values
  rw [values]
  have h := chainView_length (ls.map (fun l => l.eval (fun _ => false)))
    (ys.map (fun _ => false)) (by simpa only [List.length_map] using size)
  simpa only [List.length_map] using h

def restrictAssignment {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) : Fin V.«variables» → Bool :=
  fun v => B (oldIndex V v)

def mismatchBits {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q) : List Bool :=
  List.ofFn (fun i => (forbiddenLiteral V e p i).eval A)

@[simp] theorem mismatchBits_length {q : Nat} (V : FiniteVerifier q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (mismatchBits V A e p).length = q := by simp [mismatchBits]

theorem forbiddenLiteral_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q) (i : Fin q) :
    (forbiddenLiteral V e p i).eval A = false ↔ A (V.query e i) = patternAt q p i := by
  cases hp : patternAt q p i <;> cases ha : A (V.query e i) <;>
    simp [forbiddenLiteral, Literal.eval, hp, ha]

theorem forbiddenClause_values {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (forbiddenClause V e p).map (fun l => l.eval B) =
      mismatchBits V (restrictAssignment V B) e p := by
  simp [forbiddenClause, mismatchBits, List.map_ofFn, Function.comp_def, liftLiteral, Literal.eval,
    restrictAssignment]

theorem mismatchBits_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q)
    (actual : ∀ i, A (V.query e i) = patternAt q p i) :
    (mismatchBits V A e p).any id = false := by
  apply List.any_eq_false.mpr
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  have h := (forbiddenLiteral_false V A e p i).mpr (actual i)
  simp [h]

theorem mismatchBits_true {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q) (honest : eventValue V A e = true)
    (rejected : V.accepts e (patternAt q p) = false) :
    (mismatchBits V A e p).any id = true := by
  cases h : (mismatchBits V A e p).any id with
  | true => rfl
  | false =>
    have none := List.any_eq_false.mp h
    have equal : (fun i => A (V.query e i)) = patternAt q p := by
      funext i
      apply (forbiddenLiteral_false V A e p i).mp
      have hi := none ((forbiddenLiteral V e p i).eval A)
        (List.mem_ofFn.mpr ⟨i, rfl⟩)
      cases hv : (forbiddenLiteral V e p i).eval A <;> simp_all
    have impossible : V.accepts e (patternAt q p) = true := by
      simpa only [eventValue, equal] using honest
    rw [rejected] at impossible
    contradiction

theorem mismatchFill_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (fillBits (mismatchBits V A e p)).length = q - 3 := by
  have h := fillBits_length (mismatchBits V A e p) (by simpa using hq)
  rw [mismatchBits_length] at h
  omega

def mismatchFill {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) : Bool :=
  (fillBits (mismatchBits V A e p))[j.val]'(by
    rw [mismatchFill_length V hq A e p]
    exact j.isLt)

def extendAssignment {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) : Fin (outputVariables V) → Bool :=
  Fin.addCases A (fun k : Fin (auxiliaryCount V) =>
    let pair : Fin (V.events * (patterns q).length) × Fin (q - 3) := finProdFinEquiv.symm k
    let ep : Fin V.events × PatternIndex q := finProdFinEquiv.symm pair.1
    mismatchFill V hq A ep.1 ep.2 pair.2)

@[simp] theorem extend_old {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (v : Fin V.«variables») :
    extendAssignment V hq A (oldIndex V v) = A v := by
  simp [extendAssignment, oldIndex]

@[simp] theorem extend_fresh {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) :
    extendAssignment V hq A (freshIndex V e p j) = mismatchFill V hq A e p j := by
  unfold extendAssignment freshIndex auxiliaryCount
  rw [Fin.addCases_right]
  simp only [Equiv.symm_apply_apply]

@[simp] theorem restrict_extend {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) : restrictAssignment V (extendAssignment V hq A) = A := by
  funext v
  exact extend_old V hq A v

theorem ofFn_getElem_of_length {α : Type*} (xs : List α) (n : Nat) (h : xs.length = n) :
    List.ofFn (fun i : Fin n => xs[i.val]'(by rw [h]; exact i.isLt)) = xs := by
  subst n
  exact List.ofFn_getElem

theorem extended_auxiliary_values {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (auxiliaryNames V e p).map (extendAssignment V hq A) = fillBits (mismatchBits V A e p) := by
  simp only [auxiliaryNames, List.map_ofFn, Function.comp_def, extend_fresh, mismatchFill]
  exact ofFn_getElem_of_length _ _ (mismatchFill_length V hq A e p)

theorem tautology_satisfied {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (B : Fin (outputVariables V) → Bool) :
    (tautology V hq e).eval B = true := by
  simp [tautology, Clause.eval, Literal.eval]

theorem block_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (p : PatternIndex q) : (block V hq e p).length = q - 2 := by
  by_cases accepted : V.accepts e (patternAt q p) = true
  · simp [block, accepted]
  · simp only [block, accepted, Bool.false_eq_true, ↓reduceIte]
    have size : (forbiddenClause V e p).length = (auxiliaryNames V e p).length + 3 := by
      simp only [forbiddenClause, auxiliaryNames, List.length_ofFn]
      omega
    have h := splitLong_length (forbiddenClause V e p) (auxiliaryNames V e p) size
    have auxLength : (auxiliaryNames V e p).length = q - 3 := by simp [auxiliaryNames]
    rw [auxLength] at h
    omega

theorem block_honest {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (honest : eventValue V A e = true) :
    (block V hq e p).all (fun c => c.eval (extendAssignment V hq A)) = true := by
  cases accepted : V.accepts e (patternAt q p) with
  | true => simp [block, accepted, tautology_satisfied]
  | false =>
    have good := (fillBits_correct (mismatchBits V A e p) (by simpa using hq)).mpr
      (mismatchBits_true V A e p honest accepted)
    have values := splitLong_values (forbiddenClause V e p) (auxiliaryNames V e p)
      (extendAssignment V hq A)
    rw [forbiddenClause_values, restrict_extend, extended_auxiliary_values] at values
    have all := congrArg (fun bs : List Bool => bs.all id) values
    simp only [List.all_map, Function.comp_def, id_eq] at all
    simpa only [block, accepted, Bool.false_eq_true, ↓reduceIte] using all.trans good

theorem length_flatMap_constant {α β : Type*} (xs : List α) (f : α → List β) (k : Nat)
    (lengths : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := lengths x (by simp)
    have ht := ih (fun y hy => lengths y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, hx, ht,
      Nat.add_mul, Nat.one_mul]
    omega

theorem eventBlock_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) : (eventBlock V hq e).length = 2 ^ q * (q - 2) := by
  rw [eventBlock, length_flatMap_constant _ _ (q - 2) (fun p _ => block_length V hq e p)]
  simp only [List.length_finRange, patterns_length]

theorem convert_clause_count {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) :
    (convert V hq).clauses.length = V.events * (2 ^ q * (q - 2)) := by
  change ((List.finRange V.events).flatMap (eventBlock V hq)).length = _
  rw [length_flatMap_constant _ _ _ (fun e _ => eventBlock_length V hq e)]
  rw [List.length_finRange]

theorem convert_nonempty {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (eventsPositive : 0 < V.events) : (convert V hq).clauses ≠ [] := by
  have p : 0 < (convert V hq).clauses.length := by
    rw [convert_clause_count]
    exact Nat.mul_pos eventsPositive (Nat.mul_pos (Nat.pow_pos (by decide)) (by omega))
  intro empty
  simp only [empty, List.length_nil] at p
  omega

theorem convert_completeness {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (honest : ∀ e, eventValue V A e = true) :
    (convert V hq).Satisfiable := by
  refine ⟨extendAssignment V hq A, fun c hc => ?_⟩
  obtain ⟨e, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨p, _, hc⟩ := List.mem_flatMap.mp hc
  exact List.all_eq_true.mp (block_honest V hq A e p (honest e)) c hc

theorem clauseFailures_append {n : Nat} (xs ys : List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs ++ ys) A = clauseFailures xs A + clauseFailures ys A := by
  simp [clauseFailures, List.map_append, List.count_append]

theorem clauseFailures_le_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) (x : α) (hx : x ∈ xs) :
    clauseFailures (f x) A ≤ clauseFailures (xs.flatMap f) A := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [List.flatMap_cons, clauseFailures_append]
      omega
    · have h := ih hx
      simp only [List.flatMap_cons, clauseFailures_append]
      omega

theorem block_failed {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events) (p : PatternIndex q)
    (rejected : V.accepts e (patternAt q p) = false)
    (actual : ∀ i, restrictAssignment V B (V.query e i) = patternAt q p i) :
    1 ≤ clauseFailures (block V hq e p) B := by
  have bitsFalse := mismatchBits_false V (restrictAssignment V B) e p actual
  have size : ((forbiddenClause V e p).map (fun l => l.eval B)).length =
      ((auxiliaryNames V e p).map B).length + 3 := by
    simp only [List.length_map, forbiddenClause, auxiliaryNames, List.length_ofFn]
    omega
  have failed := chainView_failed ((forbiddenClause V e p).map (fun l => l.eval B))
    ((auxiliaryNames V e p).map B) size (by
      rw [forbiddenClause_values]
      exact bitsFalse)
  simpa only [block, rejected, Bool.false_eq_true, ↓reduceIte, clauseFailures,
    splitLong_values] using failed

theorem eventBlock_failed {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events)
    (rejected : eventValue V (restrictAssignment V B) e = false) :
    1 ≤ clauseFailures (eventBlock V hq e) B := by
  obtain ⟨p, hp⟩ := patternAt_surjective q (fun i => restrictAssignment V B (V.query e i))
  have rejectedPattern : V.accepts e (patternAt q p) = false := by
    rw [hp]
    exact rejected
  have failed := block_failed V hq B e p rejectedPattern (fun i => (congrFun hp i).symm)
  exact failed.trans (clauseFailures_le_flatMap (List.finRange (patterns q).length)
    (block V hq e) B p (by simp))

theorem count_false_map_sum {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map f).count false = (xs.map (fun x => if f x then 0 else 1)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

theorem clauseFailures_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs.flatMap f) A = (xs.map (fun x => clauseFailures (f x) A)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, clauseFailures_append, List.map_cons, List.sum_cons, ih]

theorem nat_sum_map_le {α : Type*} (xs : List α) (f g : α → Nat)
    (bound : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (bound x (by simp)) (ih (fun y hy => bound y (by simp [hy])))

theorem convert_count_bridge {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) :
    rejectedEventCount V (restrictAssignment V B) ≤ NameCompaction.failedCount (convert V hq) B := by
  change ((List.finRange V.events).map (eventValue V (restrictAssignment V B))).count false ≤
    clauseFailures ((List.finRange V.events).flatMap (eventBlock V hq)) B
  rw [count_false_map_sum, clauseFailures_flatMap]
  apply nat_sum_map_le
  intro e _
  cases rejected : eventValue V (restrictAssignment V B) e with
  | false => simpa only [rejected, Bool.false_eq_true, ↓reduceIte] using
      eventBlock_failed V hq B e rejected
  | true => simp only [↓reduceIte, Nat.zero_le]

theorem convert_gap {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (a b : Nat)
    (gap : ∀ A, a * V.events ≤ b * rejectedEventCount V A)
    (B : Fin (outputVariables V) → Bool) :
    a * (convert V hq).clauses.length ≤
      (b * (2 ^ q * (q - 2))) * NameCompaction.failedCount (convert V hq) B := by
  have eventGap := gap (restrictAssignment V B)
  have countBound := Nat.mul_le_mul_left b (convert_count_bridge V hq B)
  rw [convert_clause_count]
  calc
    a * (V.events * (2 ^ q * (q - 2))) = (a * V.events) * (2 ^ q * (q - 2)) := by
      rw [Nat.mul_assoc]
    _ ≤ (b * NameCompaction.failedCount (convert V hq) B) * (2 ^ q * (q - 2)) :=
      Nat.mul_le_mul_right _ (eventGap.trans countBound)
    _ = (b * (2 ^ q * (q - 2))) * NameCompaction.failedCount (convert V hq) B := by ac_rfl

theorem twelve_query_factor : 2 ^ 12 * (12 - 2) = 40960 := by decide

theorem twelve_query_clause_count (V : FiniteVerifier 12) :
    (convert V (by decide)).clauses.length = V.events * 40960 := by
  simpa only [twelve_query_factor] using convert_clause_count V (by decide)

def padLiteral {n : Nat} (l : Literal n) : Literal (n + 1) :=
  ⟨Fin.castAdd 1 l.variableIndex, l.positive⟩

def padClause {n : Nat} (c : Clause n) : Clause (n + 1) :=
  #v[padLiteral (c)[0], padLiteral (c)[1], padLiteral (c)[2]]

def padTautology (n : Nat) : Clause (n + 1) :=
  let v := Fin.natAdd n (0 : Fin 1)
  #v[⟨v, true⟩, ⟨v, false⟩, ⟨v, true⟩]

def padInput (F : Formula) : Formula where
  «variables» := F.«variables» + 1
  clauses := F.clauses.map padClause ++ [padTautology F.«variables»]

theorem padClause_eval {n : Nat} (c : Clause n) (B : Fin (n + 1) → Bool) :
    (padClause c).eval B = c.eval (fun v => B (Fin.castAdd 1 v)) := rfl

theorem padTautology_satisfied (n : Nat) (B : Fin (n + 1) → Bool) :
    (padTautology n).eval B = true := by
  simp [padTautology, Clause.eval, Literal.eval]

theorem padInput_satisfiable_iff (F : Formula) : (padInput F).Satisfiable ↔ F.Satisfiable := by
  change (∃ B : Fin (F.«variables» + 1) → Bool,
    ∀ c ∈ F.clauses.map padClause ++ [padTautology F.«variables»], c.eval B = true) ↔ _
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨fun v => B (Fin.castAdd 1 v), fun c hc => ?_⟩
    have hmem : padClause c ∈ (padInput F).clauses := by
      apply List.mem_append.mpr
      exact Or.inl (List.mem_map.mpr ⟨c, hc, rfl⟩)
    exact (padClause_eval c B).symm.trans (hB _ hmem)
  · rintro ⟨A, hA⟩
    let B : Fin (F.«variables» + 1) → Bool := Fin.addCases A (fun _ => false)
    refine ⟨B, fun c hc => ?_⟩
    rcases List.mem_append.mp hc with original | padding
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp original
      have h := hA d hd
      simpa only [padClause_eval, B, Fin.addCases_left] using h
    · have hc : c = padTautology F.«variables» := by simpa using padding
      subst c
      exact padTautology_satisfied F.«variables» B

@[simp] theorem padInput_clause_count (F : Formula) :
    (padInput F).clauses.length = F.clauses.length + 1 := by simp [padInput]

theorem padInput_nonempty (F : Formula) : (padInput F).clauses ≠ [] := by
  intro empty
  have size := padInput_clause_count F
  rw [empty, List.length_nil] at size
  omega

def prepareInput (F : Formula) : Formula := NameCompaction.compact (padInput F)

theorem prepareInput_satisfiable_iff (F : Formula) :
    (prepareInput F).Satisfiable ↔ F.Satisfiable :=
  (NameCompaction.compact_satisfiable_iff (padInput F)).trans (padInput_satisfiable_iff F)

theorem prepareInput_clause_count (F : Formula) :
    (prepareInput F).clauses.length = F.clauses.length + 1 := by
  simp only [prepareInput, NameCompaction.compact_clause_count, padInput_clause_count]

theorem prepareInput_nonempty (F : Formula) : (prepareInput F).clauses ≠ [] := by
  intro empty
  have h := prepareInput_clause_count F
  rw [empty, List.length_nil] at h
  omega

theorem prepareInput_variable_bound (F : Formula) :
    (prepareInput F).«variables» ≤ 3 * (F.clauses.length + 1) := by
  simpa only [prepareInput, padInput_clause_count] using NameCompaction.compact_active_bound (padInput F)

end MinUncutGames.Foundations.PCP.VerifierToCNF

end

end OAI
