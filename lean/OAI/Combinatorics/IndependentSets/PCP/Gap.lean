import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.PreprocessingTableSpectral
import OAI.Combinatorics.IndependentSets.Expansion.PoweringTableSemantics
import OAI.Combinatorics.IndependentSets.PCP.AlphabetGraphBounds
import OAI.Combinatorics.IndependentSets.PCP.RawInitialTables

namespace OAI

noncomputable section
namespace IndependentSetsGames.Foundations.PCP.FiniteGraph
namespace Bundle
variable {A : Type}

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

end Bundle

end IndependentSetsGames.Foundations.PCP.FiniteGraph

end
namespace IndependentSetsGames.Foundations.PCP.FinalConstants

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

end IndependentSetsGames.Foundations.PCP.FinalConstants
namespace IndependentSetsGames.Foundations.PCP.RoundTables

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

end IndependentSetsGames.Foundations.PCP.RoundTables

end OAI
