import OAI.NumberTheory.Ostmann.Construction.InitialSelectedPrior
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRecursiveTemplateCaps

namespace OAI

/-! # The actual selected compensation cells as one common prime-space prior -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def selectedCompensationPrior (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D P : Finset ℕ) (centers : List ℕ) (n : ℕ) : P → ℝ :=
  primeSubsetPrior P (selectedTailCellPrimes A B N X hi D ((centers.drop n).headD 0))

noncomputable def selectedCompensationCenter (centers : List ℕ) (n : ℕ) : ℝ :=
  ((centers.drop n).headD 0 : ℕ) + 1

theorem selectedCompensationPrior_nonneg (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D P : Finset ℕ) (centers : List ℕ) (n : ℕ) (q : P) :
    0 ≤ selectedCompensationPrior A B N X hi D P centers n q :=
  primeSubsetPrior_nonneg P _ q

/-- This support bound is valid at every index, including unused indices.
It therefore supplies the recursive cap without any tail-of-list premise. -/
theorem selectedCompensationPrior_lower (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D P : Finset ℕ) (centers : List ℕ) (n : ℕ) (q : P)
    (hq : selectedCompensationPrior A B N X hi D P centers n q ≠ 0) :
    Real.exp (selectedCompensationCenter centers n - 1) ≤ (q : ℝ) := by
  have hp := primeSubsetPrior_support P _ q hq
  have hc := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).1
  have hb := (mem_primeLogCellSet_iff.mp hc).2.2.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_primeLogCellSet_iff.mp hc).1.pos
  have he := (Real.lt_log_iff_exp_lt hq0).mp hb
  simpa only [selectedCompensationCenter, add_sub_cancel_right] using he.le

theorem selectedCompensationPrior_properties
    {A B : Set ℕ} {N hi : ℕ} {a C L X target : ℝ} {D P : Finset ℕ}
    {centers : List ℕ} {n : ℕ}
    (h : SelectedSmallTailCell A B N a C L X hi D target ((centers.drop n).headD 0))
    (hsub : selectedTailCellPrimes A B N X hi D ((centers.drop n).headD 0) ⊆ P) :
    (∑ q : P, selectedCompensationPrior A B N X hi D P centers n q) = 1 ∧
      (∀ q : P, (q : ℝ) * selectedCompensationPrior A B N X hi D P centers n q ≤ Real.exp (2 * L)) ∧
      (∀ q : P, selectedCompensationPrior A B N X hi D P centers n q ≠ 0 →
        (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N q) ∧
          residueDensity (tailDensityMask A N q) ≤ 2 / 3) := by
  have hh := h.prior_properties P hsub
  exact ⟨hh.1, hh.2.2.1, hh.2.2.2.2⟩

end Ostmann

end OAI
