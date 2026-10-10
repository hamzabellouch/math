import Mathlib
import OAI.Computability.VertexCover.PCP.AlphabetTableTable
import OAI.Computability.VertexCover.PCP.AlphabetGraphBounds

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.AlphabetTableBounds

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

end UniqueGames.Foundations.PCP.AlphabetTableBounds

end OAI
