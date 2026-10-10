import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.ChargesCovered

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem markedDemand_iff (as : List MarkedChild) :
    markedDemand as = true ↔ ∃ a ∈ as, a.required = true := by
  induction as with
  | nil => simp [markedDemand]
  | cons a as ih => simp [markedDemand, ih, or_and_right, exists_or]

theorem priority_charges_covered (as : List MarkedChild) (t : ℕ)
    (hs : as.Pairwise (fun a b => a.priority ≤ b.priority))
    (ht : ∃ b ∈ as, b.required = true ∧ t ≤ b.priority) :
    ChargesCovered (fun a => decide (a.priority < t)) as := by
  intro pre a post heq _ hcharge
  have ha : a.priority < t := of_decide_eq_true hcharge
  rcases ht with ⟨b, hb, hbr, hbt⟩
  rw [heq, List.mem_append] at hb
  have hp := List.pairwise_append.mp (heq ▸ hs)
  have hbp : b ∈ post := by
    rcases hb with hb | hb
    · have hle := hp.2.2 b hb a (by simp)
      omega
    · simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · omega
      · exact hb
  exact (markedDemand_iff post).mpr ⟨b, hbp, hbr⟩

theorem marked_visitation_priority (as : List MarkedChild) (t : ℕ)
    (hs : as.Pairwise (fun a b => a.priority ≤ b.priority))
    (ht : ∃ b ∈ as, b.required = true ∧ t ≤ b.priority) :
    markedGood (markedCheck as) ≤
      (as.map (chargedFactor (fun a => decide (a.priority < t)))).prod :=
  marked_visitation_charged _ _ (priority_charges_covered as t hs ht)

end SharpTerminalLeave

end

end OAI
