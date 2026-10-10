import OAI.NumberTheory.EgyptianFractions.CyclicDiscrepancyAutomatic
import OAI.NumberTheory.EgyptianFractions.RationalCommonModulus
import OAI.NumberTheory.EgyptianFractions.RationalPhaseCharacter
import OAI.NumberTheory.EgyptianFractions.FejerExponentialBudget

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Sharp lower-interval discrepancy for rational phases, using a sufficiently
large common cyclic modulus. There is no common-denominator hypothesis and
there are no modulus-size side conditions on the conclusion. -/
theorem rational_small_interval_of_fourier {Ω : Type*} [Fintype Ω]
    (x : Ω → ℚ) (hx0 : ∀ ω, 0 ≤ x ω) (hx1 : ∀ ω, x ω < 1) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖∑ ω : Ω, (Circle.exp (2 * Real.pi * (x ω : ℝ)) : ℂ) ^ l‖ ≤
        (Fintype.card Ω : ℝ) * δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω => (x ω : ℝ) < δ)).card : ℝ) := by
  classical
  obtain ⟨q, _, hq, y, hy⟩ := exists_large_common_zmod x hx0 hx1 0
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hyR (ω : Ω) : ((y ω).val : ℝ) / q = (x ω : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using
      congrArg (fun z : ℚ => (z : ℝ)) (hy ω)
  have hF : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖∑ ω : Ω, ZMod.stdAddChar ((l : ZMod q) * y ω)‖ ≤
        (Fintype.card Ω : ℝ) * δ ^ 3 := by
    intro l hl hlH
    rw [stdAddChar_sum_of_val_div Finset.univ y (fun ω => (x ω : ℝ))
      (fun ω _ => hyR ω) l]
    exact hfourier l hl hlH
  have hc := CyclicSmoothing.cyclic_small_interval_of_fourier_automatic y δ hδ hsmall hF
  have hmem (ω : Ω) : ((y ω).val : ℝ) < δ * q ↔ (x ω : ℝ) < δ := by
    rw [← hyR ω]
    exact (div_lt_iff₀ hqR).symm
  simpa only [hmem] using hc

/-- Finset-indexed rational discrepancy, including an empty sample set. -/
theorem rational_small_interval_of_fourier_finset {Ω : Type*}
    (samples : Finset Ω) (x : Ω → ℚ)
    (hx0 : ∀ ω ∈ samples, 0 ≤ x ω) (hx1 : ∀ ω ∈ samples, x ω < 1) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖∑ ω ∈ samples, (Circle.exp (2 * Real.pi * (x ω : ℝ)) : ℂ) ^ l‖ ≤
        (samples.card : ℝ) * δ ^ 3) :
    (δ / 2) * (samples.card : ℝ) ≤
      ((samples.filter (fun ω => (x ω : ℝ) < δ)).card : ℝ) := by
  classical
  have hF : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖∑ ω : samples, (Circle.exp (2 * Real.pi * (x ω : ℝ)) : ℂ) ^ l‖ ≤
        (Fintype.card samples : ℝ) * δ ^ 3 := by
    intro l hl hlH
    rw [Finset.sum_coe_sort samples
      (fun ω => (Circle.exp (2 * Real.pi * (x ω : ℝ)) : ℂ) ^ l), Fintype.card_coe]
    exact hfourier l hl hlH
  have hc := rational_small_interval_of_fourier (fun ω : samples => x ω)
    (fun ω => hx0 ω ω.property) (fun ω => hx1 ω ω.property) δ hδ hsmall hF
  have hcard : (Finset.univ.filter (fun ω : samples => (x ω : ℝ) < δ)).card =
      (samples.filter (fun ω => (x ω : ℝ) < δ)).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Finset.sum_coe_sort samples (fun ω => if (x ω : ℝ) < δ then 1 else 0)
  simpa only [Fintype.card_coe, hcard] using hc

/-- The sharp exponential localization form, uniform over all finite rational
sample families once the scale is sufficiently large. -/
theorem eventually_rational_exponential_interval {Ω : Type*}
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ w : ℝ in Filter.atTop, ∀ (samples : Finset Ω) (x : Ω → ℚ),
      (∀ ω ∈ samples, 0 ≤ x ω) → (∀ ω ∈ samples, x ω < 1) →
      (∀ l : ℕ, 1 ≤ l → l ≤ ⌊Real.exp (4 * η * w)⌋₊ →
        ‖∑ ω ∈ samples, (Circle.exp (2 * Real.pi * (x ω : ℝ)) : ℂ) ^ l‖ ≤
          (samples.card : ℝ) * Real.exp (-3 * η * w)) →
      (Real.exp (-η * w) / 2) * (samples.card : ℝ) ≤
        ((samples.filter (fun ω => (x ω : ℝ) < Real.exp (-η * w))).card : ℝ) := by
  filter_upwards [FejerParameters.eventually_fejer_exponential_parameters η hη] with w hw
  obtain ⟨hδ, hsmall, hpow, hfreq⟩ := hw
  intro samples x hx0 hx1 hfourier
  apply rational_small_interval_of_fourier_finset samples x hx0 hx1 _ hδ hsmall
  intro l hl hlH
  rw [hfreq] at hlH
  rw [hpow]
  exact hfourier l hl hlH

end Problem337

end

end OAI
