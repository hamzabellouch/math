import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.Semantics2

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetGraphBounds

open scoped BigOperators

abbrev OutputVertex (V E A : Type*) :=
  QueryIncidence.Vertex (AlphabetGraph.Event E A) (AlphabetGraph.Address V E A)

abbrev OutputDart (E A : Type*) := QueryIncidence.Dart (AlphabetGraph.Event E A) 6

def localEventFactor (q : Nat) : Nat :=
  4 * (2 * 2 ^ q) * (2 ^ (q * q)) ^ 5

def vertexFactor (q : Nat) : Nat := localEventFactor q + 2 ^ (q * q)

def dartFactor (q : Nat) : Nat := 12 * localEventFactor q

def sizeFactor (q : Nat) : Nat := 2 ^ q + vertexFactor q + dartFactor q

theorem sizeFactor_positive (q : Nat) : 0 < sizeFactor q := by
  have hp : (0 : Nat) < 2 ^ q := pow_pos (by decide) q
  unfold sizeFactor
  omega

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem gap_transfer_real [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : ConstraintGraph V E A) (eps : ℝ) (_eps_nonnegative : 0 ≤ eps)
    (source : ∀ labeling : V → A,
      eps * (Fintype.card E : ℝ) ≤ (G.rejectionCount labeling : ℝ))
    (labeling : OutputVertex V E A → QueryIncidence.Label 6) :
    (eps / 12288) * (Fintype.card (OutputDart E A) : ℝ) ≤
      ((AlphabetGraph.graph G).rejectionCount labeling : ℝ) := by
  let assignment := QueryIncidence.decodedAssignment (by decide : 0 < 6) labeling
  have htest :
      (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (G.rejectionCount (AlphabetGraph.decodedLabeling assignment) : ℝ) ≤
        2048 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) := by
    exact_mod_cast AlphabetGraph.rejection_count_bound G assignment
  have hinc :
      2 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) ≤
        ((AlphabetGraph.graph G).rejectionCount labeling : ℝ) := by
    exact_mod_cast QueryIncidence.rejection_count_bound
      (AlphabetGraph.verifier G) (by decide : 0 < 6) labeling
  have hscaled :
      eps * (Fintype.card E : ℝ) * (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) ≤
        2048 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) := by
    calc
      _ = (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (eps * (Fintype.card E : ℝ)) := by ring
      _ ≤ (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (G.rejectionCount (AlphabetGraph.decodedLabeling assignment) : ℝ) :=
        mul_le_mul_of_nonneg_left (source (AlphabetGraph.decodedLabeling assignment))
          (Nat.cast_nonneg _)
      _ ≤ _ := htest
  change (eps / 12288) *
    (Fintype.card (QueryIncidence.Dart (AlphabetGraph.Event E A) 6) : ℝ) ≤ _
  rw [QueryIncidence.card_dart, AlphabetGraph.card_event]
  push_cast
  nlinarith

omit [Nonempty A]

variable [Fintype V] [Fintype E]

theorem card_output_vertex :
    Fintype.card (OutputVertex V E A) =
      Fintype.card V * 2 ^ Fintype.card A +
        Fintype.card E * vertexFactor (Fintype.card A) := by
  rw [QueryIncidence.card_vertex, AlphabetGraph.card_event,
    AlphabetGraph.card_address, AlphabetGraph.card_localEvent]
  unfold vertexFactor localEventFactor
  ring

theorem card_output_dart :
    Fintype.card (OutputDart E A) = Fintype.card E * dartFactor (Fintype.card A) := by
  rw [QueryIncidence.card_dart, AlphabetGraph.card_event, AlphabetGraph.card_localEvent]
  unfold dartFactor localEventFactor
  ring

theorem card_output_total :
    Fintype.card (OutputVertex V E A) + Fintype.card (OutputDart E A) =
      Fintype.card V * 2 ^ Fintype.card A +
        Fintype.card E * (vertexFactor (Fintype.card A) + dartFactor (Fintype.card A)) := by
  rw [card_output_vertex, card_output_dart]
  ring

theorem card_output_total_le :
    Fintype.card (OutputVertex V E A) + Fintype.card (OutputDart E A) ≤
      sizeFactor (Fintype.card A) * (Fintype.card V + Fintype.card E) := by
  rw [card_output_total]
  have hv : 2 ^ Fintype.card A ≤ sizeFactor (Fintype.card A) := by
    unfold sizeFactor
    omega
  have he : vertexFactor (Fintype.card A) + dartFactor (Fintype.card A) ≤
      sizeFactor (Fintype.card A) := by
    unfold sizeFactor
    exact Nat.add_le_add_right (Nat.le_add_left _ _) _
  calc
    _ ≤ Fintype.card V * sizeFactor (Fintype.card A) +
        Fintype.card E * sizeFactor (Fintype.card A) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hv) (Nat.mul_le_mul_left _ he)
    _ = _ := by ring

theorem card_output_vertex_le :
    Fintype.card (OutputVertex V E A) ≤
      sizeFactor (Fintype.card A) * (Fintype.card V + Fintype.card E) :=
  (Nat.le_add_right _ _).trans card_output_total_le

theorem card_output_dart_le :
    Fintype.card (OutputDart E A) ≤
      sizeFactor (Fintype.card A) * (Fintype.card V + Fintype.card E) :=
  (Nat.le_add_left _ _).trans card_output_total_le

end IndependentSetsGames.Foundations.PCP.AlphabetGraphBounds

namespace IndependentSetsGames.Foundations.PCP.AlphabetTableBounds

open AlphabetTable

variable {q : Nat}

theorem gap_transfer_real (hq : 0 < q) (input : GenericGraphTables.Table q)
    (eps : ℝ) (eps_nonnegative : 0 ≤ eps)
    (source : ∀ labeling : Fin input.vertices → Fin q,
      eps * (input.darts : ℝ) ≤
        ((GenericGraphTables.semantics input).rejectionCount labeling : ℝ))
    (labeling : Fin (Table.build input).vertices → GraphTables.Label) :
    (eps / 12288) * ((Table.build input).darts : ℝ) ≤
      ((GraphTables.semantics (Table.build input)).rejectionCount labeling : ℝ) := by
  classical
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let lifted := fun vertex => Enumeration.labelEquiv.symm
    (labeling (Enumeration.vertexEquiv input.vertices input.darts q vertex))
  have h := AlphabetGraphBounds.gap_transfer_real
    (GenericGraphTables.semantics input) eps eps_nonnegative
    (by simpa only [Fintype.card_fin] using source) lifted
  rw [Enumeration.card_dart] at h
  have counts := Table.rejectionCount_build input lifted
  have restored : (fun v : Fin (Table.build input).vertices => Enumeration.labelEquiv
      (lifted ((Enumeration.vertexEquiv input.vertices input.darts q).symm v))) = labeling := by
    funext v
    dsimp only [lifted]
    rw [Enumeration.labelEquiv.apply_symm_apply]
    exact congrArg labeling
      ((Enumeration.vertexEquiv input.vertices input.darts q).apply_symm_apply v)
  rw [restored] at counts
  rw [← counts] at h
  exact h

theorem build_vertices (input : GenericGraphTables.Table q) :
    (Table.build input).vertices = input.vertices * 2 ^ q +
      input.darts * AlphabetGraphBounds.vertexFactor q := by
  rw [Table.build_vertices]
  simp only [Enumeration.vertexCount, Enumeration.eventCount, Enumeration.addressCount,
    Enumeration.localCount, Enumeration.tapeCount, Enumeration.pairTapeCount,
    Enumeration.fiveTapeCount, AlphabetGraphBounds.vertexFactor,
    AlphabetGraphBounds.localEventFactor]
  ring

theorem build_darts (input : GenericGraphTables.Table q) :
    (Table.build input).darts = input.darts * AlphabetGraphBounds.dartFactor q := by
  rw [Table.build_darts]
  simp only [Enumeration.dartCount, Enumeration.eventCount, Enumeration.localCount,
    Enumeration.tapeCount, Enumeration.pairTapeCount, Enumeration.fiveTapeCount,
    AlphabetGraphBounds.dartFactor, AlphabetGraphBounds.localEventFactor]
  ring

theorem build_total (input : GenericGraphTables.Table q) :
    (Table.build input).vertices + (Table.build input).darts =
      input.vertices * 2 ^ q + input.darts *
        (AlphabetGraphBounds.vertexFactor q + AlphabetGraphBounds.dartFactor q) := by
  rw [build_vertices, build_darts]
  ring

theorem build_total_le (input : GenericGraphTables.Table q) :
    (Table.build input).vertices + (Table.build input).darts ≤
      AlphabetGraphBounds.sizeFactor q * (input.vertices + input.darts) := by
  rw [build_total]
  have hv : 2 ^ q ≤ AlphabetGraphBounds.sizeFactor q := by
    unfold AlphabetGraphBounds.sizeFactor
    omega
  have he : AlphabetGraphBounds.vertexFactor q + AlphabetGraphBounds.dartFactor q ≤
      AlphabetGraphBounds.sizeFactor q := by
    unfold AlphabetGraphBounds.sizeFactor
    exact Nat.add_le_add_right (Nat.le_add_left _ _) _
  calc
    _ ≤ input.vertices * AlphabetGraphBounds.sizeFactor q +
        input.darts * AlphabetGraphBounds.sizeFactor q :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hv) (Nat.mul_le_mul_left _ he)
    _ = _ := by ring

theorem build_vertices_le (input : GenericGraphTables.Table q) :
    (Table.build input).vertices ≤
      AlphabetGraphBounds.sizeFactor q * (input.vertices + input.darts) :=
  (Nat.le_add_right _ _).trans (build_total_le input)

theorem build_darts_le (input : GenericGraphTables.Table q) :
    (Table.build input).darts ≤
      AlphabetGraphBounds.sizeFactor q * (input.vertices + input.darts) :=
  (Nat.le_add_left _ _).trans (build_total_le input)

theorem sizeFactor_positive : 0 < AlphabetGraphBounds.sizeFactor q :=
  AlphabetGraphBounds.sizeFactor_positive q

end IndependentSetsGames.Foundations.PCP.AlphabetTableBounds

end OAI
