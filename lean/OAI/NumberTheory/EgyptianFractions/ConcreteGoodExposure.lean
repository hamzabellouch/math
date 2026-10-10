import OAI.NumberTheory.EgyptianFractions.ExposedCorrelation
import OAI.NumberTheory.EgyptianFractions.RandomProductParameters

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.RandomProducts

/-- Allows the wider prime pool with upper endpoint `S^101`. -/
lemma fresh_wide_product_le_exp {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) :
    (S ^ 101) ^ freshLength S V ≤ Real.exp ((4 / 5 : ℝ) * V) := by
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hSpos : 0 < S := by linarith
  have hVpos : 0 < V := by nlinarith
  have hf := (freshLength_bounds hS hV).2
  have hc := (le_div_iff₀ (by positivity : 0 < 100 * Real.log S)).mp hf
  apply (Real.log_le_iff_le_exp (by positivity :
    0 < (S ^ 101) ^ freshLength S V)).mp
  rw [Real.log_pow, Real.log_pow]
  push_cast
  nlinarith

lemma fresh_wide_samples_lt_modulus {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) (q : ℕ)
    (hq : Real.exp ((9 / 10 : ℝ) * V) ≤ (q : ℝ))
    (p : Fin (freshLength S V) → ℕ) (hp : ∀ i, (p i : ℝ) ≤ S ^ 101) :
    (∏ i, p i) < q := by
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hVpos : 0 < V := by nlinarith
  have hprod : ((∏ i, p i : ℕ) : ℝ) ≤ (S ^ 101) ^ freshLength S V := by
    push_cast
    calc
      (∏ i, (p i : ℝ)) ≤ ∏ _i : Fin (freshLength S V), S ^ 101 :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun index _ => hp index)
      _ = _ := by simp
  have h : ((∏ i, p i : ℕ) : ℝ) < (q : ℝ) := calc
    _ ≤ (S ^ 101) ^ freshLength S V := hprod
    _ ≤ Real.exp ((4 / 5 : ℝ) * V) := fresh_wide_product_le_exp hS hV
    _ < Real.exp ((9 / 10 : ℝ) * V) := Real.exp_lt_exp.mpr (by nlinarith)
    _ ≤ (q : ℝ) := hq
  exact_mod_cast h

/-- Concrete good-exposure estimate, with atom decay proved rather than assumed. -/
theorem concrete_good_exposure_bound
    (S V : ℝ) (hS : 2 ≤ S) (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S)
    (P : Finset ℕ) (hPprime : ∀ p ∈ P, Nat.Prime p)
    (hPcard : S ^ 99 ≤ (P.card : ℝ))
    (hPupper : ∀ p ∈ P, (p : ℝ) ≤ S ^ 101)
    (a u : ℕ) (hu : 0 < u) [NeZero u]
    (huV : (u : ℝ) ≤ Real.exp V)
    (hq : Real.exp ((9 / 10 : ℝ) * V) ≤ ((u / a.gcd u : ℕ) : ℝ))
    (t : ZMod u) :
    ‖(∑ w₁ : Fin (freshLength S V) → ↥P,
      ∑ w₂ : Fin (freshLength S V) → ↥P,
      ZMod.stdAddChar
        (((a * (∏ i, (w₁ i : ℕ)) * (∏ i, (w₂ i : ℕ)) : ℕ) : ZMod u) - t)) /
        ((P.card : ℂ)^freshLength S V)^2‖ ≤ Real.exp (-V / 5) := by
  have hSpos : 0 < S := by linarith
  have hcardpos : 0 < (P.card : ℝ) := lt_of_lt_of_le (by positivity) hPcard
  have hne : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast hcardpos)
  let : NeZero (u / a.gcd u) := ⟨(reduced_modulus_pos a u hu).ne'⟩
  have hsmall (w : Fin (freshLength S V) → ↥P) :
      (∏ i, (w i : ℕ)) < u / a.gcd u :=
    fresh_wide_samples_lt_modulus (by linarith) hV _ hq
      (fun i => (w i : ℕ)) (fun i => hPupper _ (w i).property)
  apply exposed_prime_correlation_le_exp P hPprime hne (freshLength S V) a u hu hsmall t V huV
  have heq : -(7 / 10 : ℝ) * V = -7 * V / 10 := by ring
  simpa only [heq] using fresh_factorial_atom_of_card P.card hS hV hVS hPcard

end Problem337.RandomProducts

end

end OAI
