import OAI.MeasureTheory.Falconer.Estimates.LocalizationSum
import OAI.MeasureTheory.Falconer.Estimates.NonstationaryPower

namespace OAI

/-!
# Absorbing the finite graph localization errors

There are at most R^(2d) rows (pairs of child cells), and a polynomial
number of cap pairs. The four model-mass inverses and the energy prefactor
cost at most R^(5d). The derivative order is chosen before the scale,
spatial laws, graph and endpoint symbols.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem graph_discarded_sum_arbitrary_power (d : ℕ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ) :
    ∃ m : ℕ, ∀ {X ι κ : Type*} [MeasurableSpace X]
      (μ : Measure X) (S : Finset ι) (K : Finset κ) (G : κ → ι → ι → Prop)
      (f : κ → ι → ι → X → ℂ),
      (∀ k ∈ K, ∀ i ∈ S, ∀ j ∈ S, Integrable (f k i j) μ) →
      ∀ {R A C B q P : ℝ}, 1 ≤ R → 0 ≤ A → 0 ≤ C → 0 ≤ B → 0 ≤ q → 0 ≤ P →
      (S.card : ℝ) ≤ R^(2*d) → (K.card : ℝ) ≤ A^2*R^(2*d) → P ≤ R^(5*d) →
      q ≤ B*R^(-(26*σ)) →
      (∀ k ∈ K, ∀ i ∈ S, ∀ j ∈ S, ¬G k i j → ‖∫ x, f k i j x ∂μ‖ ≤ C*q^m) →
      P*‖(∫ x, ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S, f k i j x ∂μ) -
        (∫ x, ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S,
          if G k i j then f k i j x else 0 ∂μ)‖ ≤ A^2*C*B^m*R^(-T) := by
  obtain ⟨m,hm⟩ := positive_power_gain_order (by positivity : 0 < 26*σ) (11*d) T
  refine ⟨m,?_⟩
  intro X ι κ _ μ S K G f hf R A C B q P hR _hA hC hB hq hP hS hK hnorm hratio herr
  have he := integrated_discarded_sum_bound μ S K G f hf (mul_nonneg hC (pow_nonneg hq m)) herr
  have hp : (R^(5*d)*R^(2*d)*R^(2*d)*R^(2*d)) = R^((11*d : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    simp only [← pow_add]
    congr 1
    omega
  have hr : R^((11*d : ℕ) : ℝ)*q^m ≤ B^m*R^(-T) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hm hR hB hq hratio
  calc
    _ ≤ P*((K.card : ℝ)*S.card*S.card*(C*q^m)) := mul_le_mul_of_nonneg_left he hP
    _ ≤ R^(5*d)*((A^2*R^(2*d))*R^(2*d)*R^(2*d)*(C*q^m)) := by
      gcongr
    _ = (A^2*C)*(R^((11*d : ℕ) : ℝ)*q^m) := by rw [← hp]; ring
    _ ≤ (A^2*C)*(B^m*R^(-T)) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by ring

end Falconer

end OAI
