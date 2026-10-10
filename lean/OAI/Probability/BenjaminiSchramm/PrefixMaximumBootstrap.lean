import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

namespace Percolation.BenjaminiSchramm

def prefixMaximum (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Finset.range (n+1)).sup' ⟨0,by simp⟩ h

lemma le_prefixMaximum (h : ℕ → ℝ) {j n : ℕ} (hj : j ≤ n) :
    h j ≤ prefixMaximum h n :=
  Finset.le_sup' h (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem prefix_max_bootstrap (h : ℕ → ℝ) (C : ℝ)
    (hrec : ∀ n, 2*h n-prefixMaximum h n ≤ C) (n : ℕ) : h n ≤ C := by
  obtain ⟨j,hj,he⟩ := (Finset.range (n+1)).exists_mem_eq_sup' ⟨0,by simp⟩ h
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hmax : prefixMaximum h j = h j := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i hi
      exact (le_prefixMaximum h (by have hh := Finset.mem_range.mp hi; omega)).trans_eq he
    · exact le_prefixMaximum h le_rfl
  have hb := hrec j
  rw [hmax] at hb
  exact (le_prefixMaximum h le_rfl).trans (he.trans_le (by linarith))

theorem exponential_prefix_max_bootstrap (h : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (hrec : ∀ n, Real.exp (2*h n-prefixMaximum h n) ≤ C) (n : ℕ) :
    Real.exp (h n) ≤ C := by
  have hb := prefix_max_bootstrap h (Real.log C)
    (fun k => by simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos _) (hrec k)) n
  exact (Real.exp_le_exp.mpr hb).trans_eq (Real.exp_log hC)

theorem prefix_square_bootstrap (h : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hrec : ∀ n, (h n)^2 ≤ C*prefixMaximum h n) (n : ℕ) : h n ≤ C := by
  obtain ⟨j,hj,he⟩ := (Finset.range (n+1)).exists_mem_eq_sup' ⟨0,by simp⟩ h
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hmax : prefixMaximum h j = h j := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i hi
      exact (le_prefixMaximum h (by have hh := Finset.mem_range.mp hi; omega)).trans_eq he
    · exact le_prefixMaximum h le_rfl
  have hb := hrec j
  rw [hmax] at hb
  have hbound : h j ≤ C := by
    by_cases hh : h j ≤ 0
    · exact hh.trans hC
    · have hp : 0 < h j := lt_of_not_ge hh
      nlinarith
  exact (le_prefixMaximum h le_rfl).trans (he.trans_le hbound)

end Percolation.BenjaminiSchramm

end OAI
