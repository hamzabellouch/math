import OAI.NumberTheory.Ostmann.Construction.ScheduledSelectedGaps

namespace OAI

/-! # A total prior extending precisely the used compensation cells

Unused indices reuse the selected top cell. The pivot exponent retains its
original zero default beyond the finite list; no extra transfer is performed.
-/
namespace Ostmann
open scoped Classical BigOperators

def completedCompensationCell (top : ℕ) (cs : List ℕ) (n : ℕ) : ℕ :=
  (cs.drop n).headD top

noncomputable def completedCompensationSets (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D : Finset ℕ) (top : ℕ) (cs : List ℕ) (n : ℕ) : Finset ℕ :=
  selectedTailCellPrimes A B N X hi D (completedCompensationCell top cs n)

noncomputable def completedCompensationPrior (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D P : Finset ℕ) (top : ℕ) (cs : List ℕ) (n : ℕ) : P → ℝ :=
  primeSubsetPrior P (completedCompensationSets A B N X hi D top cs n)

theorem completedCompensationCell_used (top : ℕ) (cs : List ℕ) (n : ℕ)
    (hn : n < cs.length) : completedCompensationCell top cs n = (cs.drop n).headD 0 := by
  unfold completedCompensationCell
  rw [list_headD_drop_get cs top n hn, list_headD_drop_get cs 0 n hn]

theorem completedCompensationPrior_used (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D P : Finset ℕ) (top : ℕ) (cs : List ℕ) (n : ℕ) (hn : n < cs.length) :
    completedCompensationPrior A B N X hi D P top cs n =
      selectedCompensationPrior A B N X hi D P cs n := by
  unfold completedCompensationPrior completedCompensationSets selectedCompensationPrior
  rw [completedCompensationCell_used top cs n hn]

theorem completedCompensationCell_selected
    {A B : Set ℕ} {N hi top : ℕ} {a C L X target : ℝ} {D : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L X hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs targets)
    (n : ℕ) :
    ∃ t, SelectedSmallTailCell A B N a C L X hi D t (completedCompensationCell top cs n) := by
  by_cases hn : n < cs.length
  · refine ⟨(targets.drop n).headD 0 / 4, ?_⟩
    rw [completedCompensationCell_used top cs n hn]
    exact forall₂_headD_drop hcs n hn
  · refine ⟨target, ?_⟩
    simpa only [completedCompensationCell, List.drop_eq_nil_of_le (Nat.le_of_not_gt hn),
      List.headD_nil] using htop

theorem completedCompensationPrior_data
    {A B : Set ℕ} {N hi top : ℕ} {a C L X target : ℝ} {D : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L X hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs targets)
    (P : Finset ℕ) (hP : initialRegularPrimeRange L ⊆ P) (n : ℕ) :
    let Q := completedCompensationSets A B N X hi D top cs n
    Q ⊆ P ∧ Real.exp (-(2 * L)) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ ∧
      (∑ p : P, completedCompensationPrior A B N X hi D P top cs n p) = 1 ∧
      (∀ p : P, 0 ≤ completedCompensationPrior A B N X hi D P top cs n p ∧
        (p : ℝ) * completedCompensationPrior A B N X hi D P top cs n p ≤ Real.exp (2 * L)) := by
  intro Q
  obtain ⟨t, ht⟩ := completedCompensationCell_selected htop hcs n
  have hQP := ht.subset_initialRegularPrimeRange.trans hP
  have hd := ht.prior_data P hQP
  exact ⟨hQP, ht.2.2.2.1, hd.1, hd.2.1⟩

theorem completedCompensationPrior_lower (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (top : ℕ) (cs : List ℕ) (n : ℕ) (q : P)
    (hq : completedCompensationPrior A B N X hi D P top cs n q ≠ 0) :
    Real.exp (selectedCompensationCenter cs n - 1) ≤ (q : ℝ) := by
  by_cases hn : n < cs.length
  · rw [completedCompensationPrior_used A B N X hi D P top cs n hn] at hq
    exact selectedCompensationPrior_lower A B N X hi D P cs n q hq
  · have he : selectedCompensationCenter cs n = 1 := by
      simp only [selectedCompensationCenter, List.drop_eq_nil_of_le (Nat.le_of_not_gt hn),
        List.headD_nil, Nat.cast_zero, zero_add]
    rw [he, sub_self, Real.exp_zero]
    exact_mod_cast (hP q q.property).one_le

end Ostmann

end OAI
