import OAI.NumberTheory.Ostmann.Arithmetic.PairedFrequencyTreeSumData

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.PairedFrequencyTreeSum
open Characters FrequencyTreeSum

def leafProportion {Q : ℕ} [NeZero Q]
    (S : List Bool → Finset (ℤ × ℤ))
    (hdiv : ∀ p s, s ∈ S p → s.1.natAbs ∣ Q ∧ s.2.natAbs ∣ Q)
    (H : Type*) {k : ℕ} {p : List Bool} (x : Assignment S k p)
    (a : ∀ q, FrequencyExposure.Coefficients H (assignmentData S hdiv x q))
    (left right : List Bool → H → (ZMod Q)ˣ → (ZMod Q)ˣ → H) (h : H) : ℝ :=
  (Nat.card {z : BinaryHaar.Leaves (ZMod Q)ˣ k //
    BinaryExposure.leafAdmissible (FrequencyExposure.constraint (assignmentData S hdiv x) a)
      (FrequencyExposure.update false left) (FrequencyExposure.update true right)
        k ([],h) z} : ℝ) / Nat.card (BinaryHaar.Leaves (ZMod Q)ˣ k)

theorem summed_leaf_proportion_le (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : NNReal, 0 < C ∧ ∃ D : ℝ, 0 < D ∧
      ∀ Q : ℕ, ∀ [NeZero Q], ∀ S : List Bool → Finset (ℤ × ℤ),
      ∀ V : List Bool → ℕ, (∀ p, 1 ≤ V p) →
      (∀ p s, s ∈ S p → (s.1 ≠ 0 ∧ s.1.natAbs ≤ V p) ∧
        (s.2 ≠ 0 ∧ s.2.natAbs ≤ V p)) →
      ∀ hdiv : ∀ p s, s ∈ S p → s.1.natAbs ∣ Q ∧ s.2.natAbs ∣ Q,
      ∀ H : Type*, ∀ k p,
      ∀ a : (x : Assignment S k p) →
        ∀ q, FrequencyExposure.Coefficients H (assignmentData S hdiv x q),
      ∀ left right : Assignment S k p → List Bool → H → (ZMod Q)ˣ → (ZMod Q)ˣ → H,
      ∀ h : Assignment S k p → H,
      (∑ x : Assignment S k p,
        leafProportion S hdiv H x (a x) (left x) (right x) (h x)) ≤
      FrequencyTreeSum.budget S (nodeBudget (C : ℝ) D ε δ V) k p := by
  obtain ⟨C,hC,hcount⟩ := FrequencyExposure.paired_frequency_leaf_count ε hε
  obtain ⟨D,hD,hbound⟩ := total_le δ hδ
  refine ⟨C,hC,D,hD,?_⟩
  intro Q _ S V hV hS hdiv H k p a left right h
  calc
    _ ≤ ∑ x : Assignment S k p, weight S (factor (C : ℝ) ε) x := by
      apply Finset.sum_le_sum
      intro x hx
      exact (hcount Q H (assignmentData S hdiv x) (a x) (left x) (right x)
        k [] (h x)).trans_eq (budget_eq_weight S hdiv C ε x)
    _ ≤ _ := hbound (C : ℝ) ε C.property hε.le S V hV hS k p

end Ostmann.Arithmetic.PairedFrequencyTreeSum

end

end OAI
