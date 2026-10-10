import OAI.Analysis.CircleDomains.Selection.PaidBlockAssembly

namespace OAI

/-! A uniform finite cost and a positive floor bound the number of jumps.
This supplies the finite pattern extraction in jump-level removal. -/

open Set
open scoped ENNReal

namespace CircleDomainRigidity

theorem exists_uniform_jump_count_bound
    {δ : ℝ} (hδ : 0 < δ) {M : ℝ≥0∞} (hM : M < ∞) :
    ∃N : ℕ, ∀n : ℕ, ∀c : Fin n → ℝ≥0∞,
      (∀i, ENNReal.ofReal δ ≤ c i) → (∑i, c i) ≤ M → n ≤ N := by
  obtain ⟨N, hN⟩ := exists_nat_gt (M.toReal / δ)
  refine ⟨N, fun n c hc hsum => ?_⟩
  have hfloor : (n : ℝ≥0∞) * ENNReal.ofReal δ ≤ M := by
    calc
      (n : ℝ≥0∞) * ENNReal.ofReal δ = ∑_i : Fin n, ENNReal.ofReal δ := by simp
      _ ≤ ∑i, c i := Finset.sum_le_sum (fun i _ => hc i)
      _ ≤ M := hsum
  have hreal : (n : ℝ) * δ ≤ M.toReal := by
    have h := ENNReal.toReal_mono hM.ne hfloor
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le] using h
  have hn : (n : ℝ) < N := (le_div_iff₀ hδ).mpr hreal |>.trans_lt hN
  exact (Nat.cast_lt.mp hn).le

end CircleDomainRigidity

end OAI
