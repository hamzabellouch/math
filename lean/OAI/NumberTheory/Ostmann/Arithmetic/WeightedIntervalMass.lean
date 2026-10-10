import OAI.NumberTheory.Ostmann.ZeroDensity.IntervalDensityTree

namespace OAI

/-! # Cumulative and interval masses of a finite weighted set -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def weightedCDF (P : Finset ℕ) (x μ : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ p ∈ P.filter (fun p => x p ≤ t), μ p

noncomputable def weightedIntervalMass (P : Finset ℕ) (x μ : ℕ → ℝ) (a b : ℝ) : ℝ :=
  ∑ p ∈ P.filter (fun p => a < x p ∧ x p ≤ b), μ p

theorem weightedCDF_mono (P : Finset ℕ) (x μ : ℕ → ℝ) (hμ : ∀ p ∈ P, 0 ≤ μ p) :
    Monotone (weightedCDF P x μ) := by
  intro a b hab
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,
      (Finset.mem_filter.mp hp).2.trans hab⟩
  · intro p hp _
    exact hμ p (Finset.mem_filter.mp hp).1

theorem weightedCDF_sub (P : Finset ℕ) (x μ : ℕ → ℝ) (a b : ℝ) (hab : a ≤ b) :
    weightedCDF P x μ b - weightedCDF P x μ a = weightedIntervalMass P x μ a b := by
  simp only [weightedCDF, weightedIntervalMass, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hpa : x p ≤ a
  · have hpb := hpa.trans hab
    simp [hpa, hpb, not_lt.mpr hpa]
  · by_cases hpb : x p ≤ b <;> simp [hpa, hpb, lt_of_not_ge hpa]

/-- The concrete density on a tree node is its actual weighted interval
mass divided by its interval length. -/
theorem intervalNodeDensity_weightedCDF {M : ℕ} (hM : 0 < M)
    (P : Finset ℕ) (x μ : ℕ → ℝ) (a L : ℝ) (hL : 0 < L) (w : List (Fin M)) :
    intervalNodeDensity (weightedCDF P x μ) a L w =
      weightedIntervalMass P x μ (intervalNode a L w).1
        ((intervalNode a L w).1 + (intervalNode a L w).2) / (intervalNode a L w).2 := by
  rw [intervalNodeDensity, weightedCDF_sub]
  exact le_add_of_nonneg_right (intervalNode_width_pos hM a L hL w).le

end Ostmann

end OAI
