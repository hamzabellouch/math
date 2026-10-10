import OAI.MeasureTheory.DyadicAvoidance.ExceptionalCenters

namespace OAI

noncomputable section

namespace Problem310.Auxiliary

open Set MeasureTheory

/-- Periodicity is preserved under topological closure. -/
theorem closure_periodic (B : Set ℝ)
    (hB : ∀ x : ℝ, x + 1 ∈ B ↔ x ∈ B) :
    ∀ x : ℝ, x + 1 ∈ closure B ↔ x ∈ closure B := by
  have heq : (Homeomorph.addRight (1 : ℝ)) ⁻¹' B = B := by
    ext x
    exact hB x
  have hc := (Homeomorph.addRight (1 : ℝ)).preimage_closure B
  rw [heq] at hc
  intro x
  change x ∈ (Homeomorph.addRight (1 : ℝ)) ⁻¹' closure B ↔ x ∈ closure B
  rw [hc]

/-- A periodic set whose closure adds no density has arbitrarily economical open
periodic enlargements. Finite unions of grid cells satisfy the closure hypothesis. -/
theorem exists_open_periodic_enlargement (B : Set ℝ)
    (hBp : ∀ x : ℝ, x + 1 ∈ B ↔ x ∈ B)
    (hBm : volume (closure B ∩ Icc (0 : ℝ) 1) = volume (B ∩ Icc (0 : ℝ) 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set ℝ, IsOpen V ∧
      (∀ x : ℝ, x + 1 ∈ V ↔ x ∈ V) ∧ B ⊆ V ∧
      volume (V ∩ Icc (0 : ℝ) 1) ≤
        volume (B ∩ Icc (0 : ℝ) 1) + ENNReal.ofReal ε := by
  obtain ⟨V, hVo, hVp, hBV, hVm⟩ := exists_open_periodic_superset
    (closure B) isClosed_closure (closure_periodic B hBp) ε hε
  exact ⟨V, hVo, hVp, subset_closure.trans hBV, by simpa [hBm] using hVm⟩

/-- Null frontier is a simple sufficient condition for the closure-density hypothesis. -/
theorem density_closure_eq_of_null_frontier (B : Set ℝ)
    (hB : volume (frontier B) = 0) :
    volume (closure B ∩ Icc (0 : ℝ) 1) = volume (B ∩ Icc (0 : ℝ) 1) := by
  apply measure_congr
  exact (closure_ae_eq_of_null_frontier hB).inter Filter.EventuallyEq.rfl

/-- Enlarging the test set can only remove exceptional centers. -/
theorem exceptionalCenters_antitone {B V : Set ℝ} (hBV : B ⊆ V)
    (N : Set ℕ) (a : ℕ → ℝ) :
    exceptionalCenters V N a ⊆ exceptionalCenters B N a := by
  rintro x ⟨t, ht, h⟩
  exact ⟨t, ht, fun n hn hm => h n hn (hBV hm)⟩

end Problem310.Auxiliary

end

end OAI
