import OAI.Combinatorics.SharpThreshold.InfluenceReindex

namespace OAI

universe u v

/-! Reindexing real-valued expectations and Dirichlet energies on finite Boolean products. -/
noncomputable section
open scoped BigOperators

namespace Problem313.Reindex

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A coordinate equivalence preserves each weighted real-valued expectation. -/
theorem sum_weight_config (e : ι ≃ κ) (p : ℝ)
    (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (config e x) = f x) :
    (∑ y, weight p y * g y) = ∑ x, weight p x * f x := by
  classical
  apply Eq.symm
  apply Fintype.sum_equiv (configEquiv e)
  intro x
  simp only [configEquiv_apply, weight_config, hfg]

/-- The squared energy at a single coordinate is preserved by reindexing. -/
theorem coordinate_energy_config
    (e : ι ≃ κ) (p : ℝ) (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (config e x) = f x) (i : ι) :
    (∑ y, weight p y *
      (g (Function.update y (e i) true) - g (Function.update y (e i) false)) ^ 2) =
      ∑ x, weight p x *
        (f (Function.update x i true) - f (Function.update x i false)) ^ 2 := by
  apply sum_weight_config e p
  intro x
  simp only [← config_update, hfg]

/-- The full Dirichlet energy is invariant under a finite coordinate equivalence. -/
theorem energy_config
    (e : ι ≃ κ) (p : ℝ) (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (config e x) = f x) :
    (∑ j, ∑ y, weight p y *
      (g (Function.update y j true) - g (Function.update y j false)) ^ 2) =
      ∑ i, ∑ x, weight p x *
        (f (Function.update x i true) - f (Function.update x i false)) ^ 2 := by
  apply Eq.symm
  apply Fintype.sum_equiv e
  intro i
  exact (coordinate_energy_config e p f g hfg i).symm

/-- Centered second moments are invariant, for any specified center. -/
theorem centered_sum_config (e : ι ≃ κ) (p c : ℝ)
    (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (config e x) = f x) :
    (∑ y, weight p y * (g y - c) ^ 2) =
      ∑ x, weight p x * (f x - c) ^ 2 := by
  apply sum_weight_config e p
  intro x
  rw [hfg]

end Problem313.Reindex

end

end OAI
