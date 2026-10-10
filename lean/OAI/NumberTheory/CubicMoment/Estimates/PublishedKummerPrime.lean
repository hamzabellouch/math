import OAI.NumberTheory.CubicMoment.Estimates.ScaledPrimeInput
import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorCharacter

namespace OAI

/-! The finite cubic prime input including the ramified part.

Thorner–Zaman, Algebra & Number Theory 13 (2019), Theorem 1.4, specialized
to the Kummer extension Q(ω, ∛v)/Q(ω). For v not a cube this is cyclic of
order three; weighting its three Frobenius classes by the cubic character
cancels the principal and possible real exceptional terms. The conductor
divides the modulus 9v supplied by cubic reciprocity (Dunn–Radziwiłł 2024,
§2, supplementary laws). Thus Nv bounded by a fixed log power suffices.
This is the same published finite-order prime input as PublishedHecke,
with units and primes above three retained, not a Gauss-sum conclusion.
Smooth weights, exclusions and convolution estimates are derived below.
-/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory
namespace CubicFirstMoment

/-- The raw prime-sum specialization. Cubes and the zero numerator are
excluded explicitly; no smooth or structured-sum estimate is assumed. -/
def KummerPrimeSiegelWalfisz : Prop :=
  ∀ A D : ℝ, 0 < A → 0 < D → ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧
    ∀ X : ℝ, X₀ ≤ X → ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ (Real.log X)^A →
      ‖primeCutoffSum (fun p => cubicSymbol p v) X‖ ≤ C*X/(Real.log X)^D

theorem weighted_kummer_prime_bound (hSW : KummerPrimeSiegelWalfisz)
    (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ a b : ℝ, X₀ ≤ a → a ≤ b →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ (Real.log a)^A → ∀ f : ℝ → ℂ,
      (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) →
      IntegrableOn (deriv f) (Set.Icc a b) →
      ‖∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), f (norm p)*cubicSymbol p v‖ ≤
        (C*b/(Real.log a)^D)*(‖f a‖+‖f b‖+∫ t in Set.Ioc a b, ‖deriv f t‖) := by
  obtain ⟨C,X₀,hC,hX₀,hbound⟩ := hSW A D hA hD
  refine ⟨C,X₀,hC,hX₀,?_⟩
  intro a b ha hab v hv hn hcon f hdiff hderiv
  have ha1 : 1 < a := hX₀.trans_le ha
  have ha0 : 0 < a := zero_lt_one.trans ha1
  apply weighted_prime_bound (fun p => cubicSymbol p v) f ha0.le hab hdiff hderiv
  intro t ht
  have hat := Real.log_le_log ha0 ht.1
  have ht0 : 0 < t := ha0.trans_le ht.1
  have hc : norm v ≤ (Real.log t)^A := hcon.trans
    (Real.rpow_le_rpow (Real.log_pos ha1).le hat hA.le)
  apply (hbound t (ha.trans ht.1) v hv hn hc).trans
  exact div_le_div₀ (mul_nonneg hC.le (ht0.le.trans ht.2))
    (mul_le_mul_of_nonneg_left ht.2 hC.le)
    (Real.rpow_pos_of_pos (Real.log_pos ha1) D)
    (Real.rpow_le_rpow (Real.log_pos ha1).le hat hD.le)

theorem scaled_kummer_prime_bound (hSW : KummerPrimeSiegelWalfisz)
    {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ (Y R M B : ℝ) (w : ℝ → ℂ),
      X₀ ≤ Y → 1 ≤ R → 0 ≤ M → 0 ≤ B → ContDiff ℝ ∞ w →
      (∀ x, x < 1 → w x = 0) → (∀ x, ‖w x‖ ≤ M) →
      (∀ x, 0 < x → ‖deriv w x‖*x ≤ B) →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      norm v ≤ (Real.log Y)^A → ∀ u : ℝ,
      ‖smoothPrimeCharacterSum R Y w (fun p => cubicSymbol p v) u‖ ≤
        (C*(R*Y)/(Real.log Y)^D)*(2*M+(R-1)*(B+M*|u|)) := by
  obtain ⟨C,X₀,hC,hX₀,hbound⟩ := weighted_kummer_prime_bound hSW A D hA hD
  refine ⟨C,X₀,hC,hX₀,?_⟩
  intro Y R M B w hYX hR hM hB hw hlo hwm hwd v hv hn hcon u
  have hY : 0 < Y := zero_lt_one.trans (hX₀.trans_le hYX)
  have hYR : Y ≤ R*Y := by nlinarith
  obtain ⟨hdiff,hderiv,hvar⟩ := rescaled_mellin_variation hw hY hR hM hB hwm hwd u
  rw [smoothPrimeCharacterSum_eq_interval hY hw.continuous hlo]
  exact (hbound Y (R*Y) hYX hYR v hv hn hcon
    (fun t => w (t/Y)*mellinPhase u t) hdiff hderiv).trans
      (mul_le_mul_of_nonneg_left hvar
        (div_nonneg (mul_nonneg hC.le (mul_nonneg (zero_le_one.trans hR) hY.le))
          (Real.rpow_nonneg (Real.log_nonneg (le_of_lt (hX₀.trans_le hYX))) _)))

end CubicFirstMoment

end

end OAI
