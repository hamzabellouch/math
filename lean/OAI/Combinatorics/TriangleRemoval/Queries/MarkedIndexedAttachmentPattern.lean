import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.RecordedCallForest
import OAI.Combinatorics.TriangleRemoval.Process.EdgeMatching
import OAI.Combinatorics.TriangleRemoval.Process.ValidIndexedAttachments

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
open Classical in

theorem marked_indexed_attachment_pattern_count {K s : ℕ}
    (E : Finset (Finset (Fin K))) (birth : Fin s → Fin K) (hE : E.card ≤ 2) (a b : Option (Fin s)) :
    Fintype.card (Σ F : {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v},
      {f // f ∈ indexedAttachmentFamily E birth F.val}) ≤ 6^s := by
  classical
  rw [Fintype.card_sigma]
  calc
    ∑ F : {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v},
        Fintype.card {f // f ∈ indexedAttachmentFamily E birth F.val}
      ≤ ∑ _F : {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v}, 2^s := by
        apply Finset.sum_le_sum
        intro F _
        simpa only [Fintype.card_coe] using fixed_forest_indexed_attachment_count E birth hE F.val
    _ = Fintype.card {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v} * 2^s := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
    _ ≤ 3^s * 2^s := Nat.mul_le_mul_right _ (PathForest.two_path_forest_count a b)
    _ = 6^s := by rw [← Nat.mul_pow]

open Classical in

theorem all_marked_indexed_attachment_pattern_count {K s : ℕ} {M : Type*} [Fintype M]
    (E : Finset (Finset (Fin K))) (birth : Fin s → Fin K) (hE : E.card ≤ 2) (mark : M → Option (Fin s)) :
    Fintype.card (Σ ab : M × M,
      Σ F : {F : PathForest s // ∀ v, F.OnPath (mark ab.1) v ∨ F.OnPath (mark ab.2) v},
        {f // f ∈ indexedAttachmentFamily E birth F.val}) ≤ (Fintype.card M)^2 * 6^s := by
  classical
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ab : M × M, 6^s := by
      apply Finset.sum_le_sum
      intro ab _
      exact marked_indexed_attachment_pattern_count E birth hE _ _
    _ = (Fintype.card M)^2 * 6^s := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,smul_eq_mul,pow_two]

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
