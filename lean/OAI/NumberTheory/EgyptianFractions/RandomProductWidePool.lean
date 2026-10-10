import OAI.NumberTheory.EgyptianFractions.RandomProductParameters

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.RandomProducts

/-- The random-product estimate only needs the coarser upper bound `S^101`:
a fixed-width prime interval is not required. -/
theorem wide_fresh_product_le_exp {S V : ℝ} (hS : 2 ≤ S)
    (hV : 100000 * Real.log S ≤ V) :
    (S ^ 101) ^ freshLength S V ≤ Real.exp ((4 / 5 : ℝ) * V) := by
  have hSone : 1 < S := by linarith
  have hSpos : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos hSone
  have hVpos : 0 < V := by nlinarith
  have hf := (freshLength_bounds hSone hV).2
  have hcross := (le_div_iff₀ (by positivity : 0 < 100 * Real.log S)).mp hf
  apply (Real.log_le_iff_le_exp (by positivity : 0 < (S ^ 101) ^ freshLength S V)).mp
  rw [Real.log_pow, Real.log_pow]
  push_cast
  nlinarith

theorem wide_fresh_samples_product_le_exp {S V : ℝ} (hS : 2 ≤ S)
    (hV : 100000 * Real.log S ≤ V)
    (p : Fin (freshLength S V) → ℕ)
    (hp : ∀ i, (p i : ℝ) ≤ S ^ 101) :
    ((∏ i, p i : ℕ) : ℝ) ≤ Real.exp ((4 / 5 : ℝ) * V) := by
  calc
    ((∏ i, p i : ℕ) : ℝ) = ∏ i, (p i : ℝ) := by norm_cast
    _ ≤ ∏ _i : Fin (freshLength S V), S ^ 101 :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun index _ => hp index)
    _ = (S ^ 101) ^ freshLength S V := by simp
    _ ≤ Real.exp ((4 / 5 : ℝ) * V) := wide_fresh_product_le_exp hS hV

theorem wide_fresh_samples_product_lt_modulus {S V : ℝ} (hS : 2 ≤ S)
    (hV : 100000 * Real.log S ≤ V) (q : ℕ)
    (hq : Real.exp ((9 / 10 : ℝ) * V) ≤ (q : ℝ))
    (p : Fin (freshLength S V) → ℕ)
    (hp : ∀ i, (p i : ℝ) ≤ S ^ 101) :
    (∏ i, p i) < q := by
  have hlog : 0 < Real.log S := Real.log_pos (by linarith)
  have hVpos : 0 < V := by nlinarith
  have hreal : ((∏ i, p i : ℕ) : ℝ) < (q : ℝ) := by
    calc
      ((∏ i, p i : ℕ) : ℝ) ≤ Real.exp ((4 / 5 : ℝ) * V) :=
        wide_fresh_samples_product_le_exp hS hV p hp
      _ < Real.exp ((9 / 10 : ℝ) * V) := Real.exp_lt_exp.mpr (by nlinarith)
      _ ≤ (q : ℝ) := hq
  exact_mod_cast hreal

end Problem337.RandomProducts

end

end OAI
