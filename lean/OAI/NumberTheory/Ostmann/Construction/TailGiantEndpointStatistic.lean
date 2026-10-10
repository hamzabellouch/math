import OAI.NumberTheory.Ostmann.Construction.CompleteTailGiantMean
import OAI.NumberTheory.Ostmann.Construction.PrimePhysicalTest

namespace OAI

/-! # The selected giant mean as the actual initial endpoint sum -/

namespace Ostmann
open scoped Classical BigOperators

theorem tailGiantPhysical_eq_primePhysicalTest (A : Set ℕ) (N : ℕ) (F : Finset ℕ)
    (p : ℕ) [Fact p.Prime] :
    tailGiantPhysical A N F p =
      primePhysicalTest (tailDensityMask A N p) true (decide (p ∈ F)) := by
  funext x
  by_cases hp : p ∈ F
  · simp [tailGiantPhysical, primePhysicalTest, hp]
  · simp [tailGiantPhysical, primePhysicalTest, hp]

theorem tailGiantEndpointMean_weighted_sum (A : Set ℕ) (N : ℕ) (F E P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (μ : P → ℝ) :
    let _ : ∀ p : P, Fact (p : ℕ).Prime := fun p => ⟨hP p p.property⟩
    (∑ p : P, μ p * tailGiantEndpointMean A N F E p) =
      (E.card : ℝ)⁻¹ * ∑ a ∈ E,
        (∑ p : P, (μ p : ℂ) * tailGiantPhysical A N F p (a : ZMod (p : ℕ))).re := by
  intro
  simp_rw [tailGiantEndpointMean_eq, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- A selected full-cell mean is a positive sum over the literal integer
endpoint set used in the initial Poisson statistic. -/
theorem tailGiantEndpointMean_endpoint_lower (A : Set ℕ) (N : ℕ) (F E P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (μ : P → ℝ) (δ : ℝ)
    (hE : E.Nonempty) (hmean : δ ≤ ∑ p : P, μ p * tailGiantEndpointMean A N F E p) :
    let _ : ∀ p : P, Fact (p : ℕ).Prime := fun p => ⟨hP p p.property⟩
    ((E.image fun a : ℕ => (a : ℤ)).card : ℝ) * δ ≤
      ∑ a ∈ E.image (fun a : ℕ => (a : ℤ)),
        (∑ p : P, (μ p : ℂ) * primePhysicalTest (tailDensityMask A N p) true
          (decide ((p : ℕ) ∈ F)) (a : ZMod (p : ℕ))).re := by
  intro
  have hc : (0 : ℝ) < E.card := Nat.cast_pos.mpr hE.card_pos
  have hi : Function.Injective (fun a : ℕ => (a : ℤ)) := by
    intro a b h
    change (a : ℤ) = (b : ℤ) at h
    exact_mod_cast h
  rw [Finset.card_image_of_injective _ hi, Finset.sum_image (fun _ _ _ _ h => hi h)]
  have hh := mul_le_mul_of_nonneg_left hmean hc.le
  rw [tailGiantEndpointMean_weighted_sum A N F E P hP μ, ← mul_assoc,
    mul_inv_cancel₀ hc.ne', one_mul] at hh
  simpa only [Int.cast_natCast, tailGiantPhysical_eq_primePhysicalTest] using hh

end Ostmann

end OAI
