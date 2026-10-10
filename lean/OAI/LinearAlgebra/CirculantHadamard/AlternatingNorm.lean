import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

namespace OAI

universe uR uIota

/-!
# Complex norms after clearing an alternating-product denominator

The integral alternating product is related to its character values by a
polynomial identity in the coefficient ring. Applying an arbitrary complex
ring homomorphism to that identity is legitimate even before knowing that the
homomorphism extends to the fraction field. Equal numbers of numerator and
denominator factors, all of the same positive norm, then force norm one.
-/

namespace CirculantHadamard.AlternatingNorm

open scoped BigOperators

theorem norm_map_prod_of_const {R : Type uR} {ι : Type uIota} [CommRing R]
    (σ : R →+* ℂ) (x : ι → R) (s : Finset ι) (c : ℝ)
    (hx : ∀ i ∈ s, ‖σ (x i)‖ = c) :
    ‖σ (∏ i ∈ s, x i)‖ = c ^ s.card := by
  classical
  rw [map_prod, norm_prod]
  calc
    (∏ i ∈ s, ‖σ (x i)‖) = ∏ _i ∈ s, c := Finset.prod_congr rfl hx
    _ = c ^ s.card := by simp

/-- The numerator and denominator have equally many character factors.
Only a genuine cleared identity in `R` is required; there is no assumed norm
bound on `z`, no injectivity assumption on `σ`, and no fraction-field extension.
-/
theorem norm_eq_one_of_balanced_products {R : Type uR} {ι : Type uIota} [CommRing R]
    (σ : R →+* ℂ) (x : ι → R) (numerator denominator : Finset ι)
    (z : R) (c : ℝ) (hc : 0 < c)
    (hcard : numerator.card = denominator.card)
    (hnumerator : ∀ i ∈ numerator, ‖σ (x i)‖ = c)
    (hdenominator : ∀ i ∈ denominator, ‖σ (x i)‖ = c)
    (hclear : z * (∏ i ∈ denominator, x i) = ∏ i ∈ numerator, x i) :
    ‖σ z‖ = 1 := by
  have hmap := congrArg σ hclear
  rw [map_mul] at hmap
  have hnorm := congrArg norm hmap
  rw [norm_mul,
    norm_map_prod_of_const σ x denominator c hdenominator,
    norm_map_prod_of_const σ x numerator c hnumerator,
    hcard] at hnorm
  have hpositive : 0 < c ^ denominator.card := pow_pos hc _
  nlinarith

end CirculantHadamard.AlternatingNorm

end OAI
