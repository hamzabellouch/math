import OAI.NumberTheory.Ostmann.Construction.InitialDoubledCutoffProduct

namespace OAI

/-! # The retained logarithmic window gives both Poisson cutoffs -/
namespace Ostmann
open scoped BigOperators

theorem sampled_product_window_of_log_error {I : Type*} [Fintype I]
    (v : I → ℕ) (hv : ∀ i, v i ≠ 0) (X Δ E : ℝ) (hX : 0 < X)
    (hlog : |Real.log (∏ i, (v i : ℝ)) - (Real.log X + Δ)| ≤ E) :
    X * Real.exp (Δ - E) ≤ ∏ i, (v i : ℝ) ∧
      (∏ i, (v i : ℝ)) ≤ X * Real.exp (Δ + E) := by
  have hp : 0 < ∏ i, (v i : ℝ) := Finset.prod_pos (fun i _ => by
    exact_mod_cast Nat.pos_of_ne_zero (hv i))
  obtain ⟨hl, hu⟩ := abs_le.mp hlog
  constructor
  · calc
      _ = Real.exp (Real.log X + (Δ - E)) := by rw [Real.exp_add, Real.exp_log hX]
      _ ≤ Real.exp (Real.log (∏ i, (v i : ℝ))) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log hp
  · calc
      _ = Real.exp (Real.log (∏ i, (v i : ℝ))) := (Real.exp_log hp).symm
      _ ≤ Real.exp (Real.log X + (Δ + E)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_add, Real.exp_log hX]

theorem sampled_product_poisson_cutoff {I : Type*} [Fintype I]
    (v : I → ℕ) (X H R : ℝ) (N : ℕ) (hX : 0 ≤ X) (hH : 0 ≤ H)
    (hupper : (∏ i, (v i : ℝ)) ≤ X * R) (hN : H * R ≤ N) :
    H * (∏ i, v i) ≤ N * X := by
  have hp : ((∏ i, v i : ℕ) : ℝ) = ∏ i, (v i : ℝ) := by push_cast; rfl
  rw [hp]
  calc
    _ ≤ H * (X * R) := mul_le_mul_of_nonneg_left hupper hH
    _ = (H * R) * X := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hN hX

/-- The cutoff weights restrict the sampled product without changing any
marginal prior. The only extra loss is the already bounded cell rounding. -/
theorem initial_doubled_product_window (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b d r : ℕ) (μ₀ : P → ℝ) (μb : Fin b → P → ℝ)
    (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ) (G cb cd : ℝ) (center : Fin r → ℝ)
    (hG : ∀ q : P, μ₀ q ≠ 0 → |Real.log (q : ℝ) - G| ≤ 1)
    (hc : ∀ i (q : P), μc i q ≠ 0 → |Real.log (q : ℝ) - center i| ≤ 1)
    (X Δ E : ℝ) (hX : 0 < X)
    (htarget : |2 * (G + cb + cd + ∑ i, center i) - (Real.log X + Δ)| ≤ E)
    (x : Fin (((b + (d + r)) + 1) + ((b + (d + r)) + 1)) → P)
    (hprior : productPrior (Fin.append
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))) x ≠ 0)
    (hw : doubledHalfWeight (fun y : Fin ((b + (d + r)) + 1) → P =>
      (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail y) : ℂ)) x ≠ 0) :
    X * Real.exp (Δ - (E + 2 * (r + 3))) ≤ ∏ i, (x i : ℝ) ∧
      (∏ i, (x i : ℝ)) ≤ X * Real.exp (Δ + (E + 2 * (r + 3))) := by
  have hlog := initial_doubled_cutoff_log_product P hP b d r μ₀ μb μd μc
    G cb cd center hG hc x hprior hw
  apply sampled_product_window_of_log_error (fun i => (x i : ℕ))
    (fun i => (hP _ (x i).property).ne_zero) X Δ (E + 2 * (r + 3)) hX
  exact (abs_sub_le _ _ _).trans (by linarith only [add_le_add hlog htarget])

end Ostmann

end OAI
