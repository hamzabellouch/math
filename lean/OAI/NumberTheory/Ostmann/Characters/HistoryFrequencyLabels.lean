import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyLabelsBasic
import OAI.NumberTheory.Ostmann.Characters.ReducedFrequencyTree

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HistoryFrequencyLabels
open HistoryReconstruction

def literalWeight (φ : List Bool → ℤ → ℤ → ℤ → ℝ) :
    (k : ℕ) → List Bool → ℤ → Tree k → ℝ
  | 0, _, _, _ => 1
  | k+1, p, s, t => φ p s t.1.1 t.1.2 *
      literalWeight φ k (false::p) t.1.1 t.2.1 *
      literalWeight φ k (true::p) t.1.2 t.2.2

@[simp] theorem literalWeight_treeOf (S : List Bool → Finset ℤ)
    (φ : List Bool → ℤ → ℤ → ℤ → ℝ) {k : ℕ} {p : List Bool}
    (x : FrequencyTreeSum.Assignment S k p) :
    literalWeight φ k p (FrequencyTreeSum.root S x) (treeOf S x) =
      FrequencyTreeSum.weight S φ x := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    change φ p x.1.val (FrequencyTreeSum.root S x.2.1) (FrequencyTreeSum.root S x.2.2) *
      literalWeight φ k (false::p) (FrequencyTreeSum.root S x.2.1) (treeOf S x.2.1) *
      literalWeight φ k (true::p) (FrequencyTreeSum.root S x.2.2) (treeOf S x.2.2) =
      φ p x.1.val (FrequencyTreeSum.root S x.2.1) (FrequencyTreeSum.root S x.2.2) *
      FrequencyTreeSum.weight S φ x.2.1 * FrequencyTreeSum.weight S φ x.2.2
    rw [ih x.2.1, ih x.2.2]

def historyTotal (S : List Bool → Finset ℤ) (φ : List Bool → ℤ → ℤ → ℤ → ℝ)
    (k : ℕ) (p : List Bool) : ℝ :=
  ∑ h : SupportedHistory S k p, literalWeight φ k p h.val.1 h.val.2

theorem historyTotal_eq (S : List Bool → Finset ℤ)
    (φ : List Bool → ℤ → ℤ → ℤ → ℝ) (k : ℕ) (p : List Bool) :
    historyTotal S φ k p = FrequencyTreeSum.total S φ k p := by
  rw [historyTotal, ← sum_reindex S k p]
  simp only [literalWeight_treeOf, FrequencyTreeSum.total]

theorem pair_sum_reindex {A : Type*} [AddCommMonoid A]
    (S T : List Bool → Finset ℤ) (k l : ℕ) (p q : List Bool)
    (F : ℤ → Tree k → ℤ → Tree l → A) :
    (∑ x : FrequencyTreeSum.Assignment S k p,
      ∑ y : FrequencyTreeSum.Assignment T l q,
        F (FrequencyTreeSum.root S x) (treeOf S x)
          (FrequencyTreeSum.root T y) (treeOf T y)) =
    ∑ h : SupportedHistory S k p, ∑ h' : SupportedHistory T l q,
      F h.val.1 h.val.2 h'.val.1 h'.val.2 := by
  simp_rw [sum_reindex T l q]
  exact sum_reindex S k p (fun s t =>
    ∑ h' : SupportedHistory T l q, F s t h'.val.1 h'.val.2)

theorem historyTotal_reduced_le (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ C : ℝ, 0 ≤ C → ∀ S : List Bool → Finset ℤ,
      ∀ V : List Bool → ℕ, (∀ p, 1 ≤ V p) →
      (∀ p s, s ∈ S p → s ≠ 0 ∧ s.natAbs ≤ V p) → ∀ k p,
      historyTotal S (ReducedFrequencyTree.factor ε C) k p ≤
        FrequencyTreeSum.budget S
          (fun p => C*(V p:ℝ)^ε*
            (2*D*(V (false::p):ℝ)^ε*(1+Real.log (V p)))) k p := by
  obtain ⟨D, hD, hb⟩ := ReducedFrequencyTree.total_le ε hε
  refine ⟨D, hD, ?_⟩
  intro C hC S V hV hS k p
  rw [historyTotal_eq]
  exact hb C hC S V hV hS k p

end Ostmann.Characters.HistoryFrequencyLabels

end

end OAI
