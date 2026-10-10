import OAI.NumberTheory.CubicMoment.Estimates.PolynomialMeanValue
import OAI.NumberTheory.CubicMoment.Estimates.RepeatedPrimeSupport
import OAI.NumberTheory.CubicMoment.Estimates.PrimeNormFibers

namespace OAI

/-!
# Mean values of the squarefree prime-convolution discrepancy

The ordinary Montgomery--Vaughan input is specialized to the actual
coefficients obtained from independent prime factors.  The full polynomial
factors exactly; removing repeated primes costs the energy already proved
in `RepeatedPrimeSupport`.  The maximum multiplicity of an integer norm is
kept explicit, so no divisor estimate is hidden in this deduction.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma theta_finset_prod {κ : Type*} (s : Finset κ) (f : κ → Eisenstein) (ℓ : ℤ) :
    theta ℓ (∏ i ∈ s, f i) = ∏ i ∈ s, theta ℓ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

lemma normTwist_finset_prod {κ : Type*} (s : Finset κ) (f : κ → Eisenstein)
    (u : ℝ) (hf : ∀ i ∈ s, f i ≠ 0) :
    normTwist u (∏ i ∈ s, f i) = ∏ i ∈ s, normTwist u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [normTwist, norm]
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, normTwist_mul u (hf i (Finset.mem_insert_self i s))
      (Finset.prod_ne_zero_iff.mpr hs), ih hs, Finset.prod_insert hi]

/-- Fixed-angle polynomial with arbitrary finite Eisenstein support. -/
def angularCoefficientPolynomial (B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (ℓ : ℤ) (u t : ℝ) : ℂ :=
  ∑ b ∈ B, β b * theta ℓ b * mellinPhase (t + u) (norm b)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product before imposing squarefreeness. The prime supports and
weights are independent, exactly as required by the structured coefficients. -/
def fullPrimeProductPolynomial (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (ℓ : ℤ) (u t : ℝ) : ℂ :=
  ∏ i, ∑ p ∈ S i, w i p * theta ℓ p * mellinPhase (t + u) (norm p)

def squarefreePrimePolynomial (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (ℓ : ℤ) (u t : ℝ) : ℂ :=
  angularCoefficientPolynomial (orderedConvolutionSupport S)
    (squarefreeConvolution S w) ℓ u t

def errorPrimePolynomial (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (ℓ : ℤ) (u t : ℝ) : ℂ :=
  angularCoefficientPolynomial (orderedConvolutionSupport S)
    (squarefreeConvolutionError S w) ℓ u t

/-- Collection by products preserves the independent prime factorization,
including the fixed angular character and the translated Mellin height. -/
theorem orderedConvolution_angular_polynomial (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (ℓ : ℤ) (u t : ℝ) :
    angularCoefficientPolynomial (orderedConvolutionSupport S)
      (orderedConvolution S w) ℓ u t = fullPrimeProductPolynomial S w ℓ u t := by
  unfold angularCoefficientPolynomial fullPrimeProductPolynomial
  simp only [← normTwist_eq_mellinPhase]
  simp_rw [mul_assoc]
  rw [orderedConvolution_sum]
  calc
    _ = ∑ f ∈ Fintype.piFinset S,
        ∏ i, w i (f i) * (theta ℓ (f i) * normTwist (t + u) (f i)) := by
      apply Finset.sum_congr rfl
      intro f hf
      have hn : ∀ i ∈ (Finset.univ : Finset ι), f i ≠ 0 := by
        intro i hi
        exact (hS i (f i) ((Fintype.mem_piFinset.mp hf) i)).2.ne_zero
      rw [theta_finset_prod, normTwist_finset_prod _ _ _ hn,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    _ = _ := (Finset.prod_univ_sum S
      (fun i p => w i p * (theta ℓ p * normTwist (t + u) p))).symm

/-- The difference between the factored polynomial and its squarefree part
has exactly the repeated-prime discrepancy coefficients. -/
theorem fullPrimeProduct_sub_squarefree (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (ℓ : ℤ) (u t : ℝ) :
    fullPrimeProductPolynomial S w ℓ u t - squarefreePrimePolynomial S w ℓ u t =
      errorPrimePolynomial S w ℓ u t := by
  rw [← orderedConvolution_angular_polynomial S w hS]
  simp only [squarefreePrimePolynomial, errorPrimePolynomial,
    angularCoefficientPolynomial, squarefreeConvolutionError,
    sub_mul, Finset.sum_sub_distrib]

/-- The actual largest multiplicity when distinct Eisenstein integers have
the same positive rational norm. -/
def normFiberMultiplicity (B : Finset Eisenstein) (Z : ℕ) : ℕ :=
  (Finset.Icc 1 Z).sup (fun n => (B.filter (fun b => normNat b = n)).card)

lemma normFiber_card_le (B : Finset Eisenstein) (Z n : ℕ)
    (hn : n ∈ Finset.Icc 1 Z) :
    ((B.filter (fun b => normNat b = n)).card : ℝ) ≤
      (normFiberMultiplicity B Z : ℝ) := by
  exact_mod_cast (Finset.le_sup (f := fun m => (B.filter (fun b => normNat b = m)).card) hn)

lemma normFiberMultiplicity_primeProducts_le (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (Z : ℕ) :
    normFiberMultiplicity (orderedConvolutionSupport S) Z ≤
      (2 * Fintype.card ι) ^ (Fintype.card ι) := by
  apply Finset.sup_le
  intro n _
  exact primeProduct_norm_fiber_card S hS n

lemma orderedConvolutionSupport_ne_zero (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) :
    ∀ b ∈ orderedConvolutionSupport S, b ≠ 0 := by
  intro b hb
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hb
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact (hS i (f i) ((Fintype.mem_piFinset.mp hf) i)).2.ne_zero

lemma orderedConvolutionSupport_normNat (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (Y : ℝ) (Z : ℕ)
    (hprod : ∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y)
    (hYZ : Y ≤ (Z : ℝ)) :
    ∀ b ∈ orderedConvolutionSupport S, normNat b ∈ Finset.Icc 1 Z := by
  intro b hb
  have hb₀ := orderedConvolutionSupport_ne_zero S hS b hb
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hb
  apply Finset.mem_Icc.mpr
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero hb₀)
  · exact_mod_cast (show (normNat (∏ i, f i) : ℝ) ≤ (Z : ℝ) by
      rw [normNat_cast]
      exact (hprod f hf).trans hYZ)

/-- The repeated-prime error inherits an actual power saving in its dyadic
mean square. The only analytic input here is the ordinary published
Montgomery--Vaughan inequality; the coefficient energy is proved. -/
theorem primeConvolutionError_dyadicMeanSquare {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y c : ℝ) (Z : ℕ),
      0 < Y → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ Y ^ c < norm p) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) → Y ≤ (Z : ℝ) →
      ∀ (ℓ : ℤ) (u T : ℝ), 0 < T →
      ((∫ t in T..2 * T, ‖errorPrimePolynomial S w ℓ u t‖ ^ 2) +
       (∫ t in -2 * T..-T, ‖errorPrimePolynomial S w ℓ u t‖ ^ 2)) / T ≤
        2 * C * (1 + (Z : ℝ) / T) *
          (normFiberMultiplicity (orderedConvolutionSupport S) Z : ℝ) *
          (K * Y ^ (1 - c / 2) *
            (((Fintype.card ι) ^ (Fintype.card ι) : ℕ) * (∏ i, M i)) ^ 2) := by
  obtain ⟨K, hK, henergy⟩ := primeConvolutionError_power_energy (ι := ι)
  refine ⟨K, hK, ?_⟩
  intro S w M Y c Z hY hM hS hprod hw hYZ ℓ u T hT
  have hprime : ∀ i, ∀ p ∈ S i, primaryPrime p := fun i p hp => (hS i p hp).1
  have hmean := fixedAngular_translated_dyadicMeanSquare hMV hC
    (orderedConvolutionSupport S) (squarefreeConvolutionError S w) Z
    (normFiberMultiplicity (orderedConvolutionSupport S) Z)
    (orderedConvolutionSupport_normNat S hprime Y Z hprod hYZ)
    (orderedConvolutionSupport_ne_zero S hprime)
    (normFiber_card_le (orderedConvolutionSupport S) Z) ℓ u hT
  exact hmean.trans (mul_le_mul_of_nonneg_left
    (henergy S w M Y c hY hM hS hprod hw) (by positivity))

/-- A character bounded by one does not increase coefficient energy,
including at primes dividing its conductor, where it may vanish. -/
lemma coefficient_twist_energy_le (B : Finset Eisenstein)
    (β χ : Eisenstein → ℂ) (hχ : ∀ b ∈ B, ‖χ b‖ ≤ 1) :
    (∑ b ∈ B, ‖β b * χ b‖ ^ 2) ≤ ∑ b ∈ B, ‖β b‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro b hb
  apply pow_le_pow_left₀ (_root_.norm_nonneg _) _ 2
  rw [norm_mul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (hχ b hb) (_root_.norm_nonneg (β b))

def twistedErrorPrimePolynomial (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (χ : Eisenstein → ℂ) (ℓ : ℤ) (u t : ℝ) : ℂ :=
  angularCoefficientPolynomial (orderedConvolutionSupport S)
    (fun b => squarefreeConvolutionError S w b * χ b) ℓ u t

/-- Both height norms required in the exceptional-moment argument retain
the repeated-prime power saving after a conductor character is inserted.
All constants are uniform in the character, angular mode, and translation. -/
theorem primeConvolutionError_twisted_height_bounds {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y c : ℝ) (Z : ℕ),
      0 < Y → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ Y ^ c < norm p) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) → Y ≤ (Z : ℝ) →
      ∀ χ : Eisenstein → ℂ,
      (∀ b ∈ orderedConvolutionSupport S, ‖χ b‖ ≤ 1) →
      ∀ (ℓ : ℤ) (u T : ℝ), 0 < T →
      (((∫ t in T..2 * T, ‖twistedErrorPrimePolynomial S w χ ℓ u t‖ ^ 2) +
        (∫ t in -2 * T..-T, ‖twistedErrorPrimePolynomial S w χ ℓ u t‖ ^ 2)) / T ≤
        2 * C * (1 + (Z : ℝ) / T) *
          (normFiberMultiplicity (orderedConvolutionSupport S) Z : ℝ) *
          (K * Y ^ (1 - c / 2) *
            (((Fintype.card ι) ^ (Fintype.card ι) : ℕ) * (∏ i, M i)) ^ 2)) ∧
      (((∫ t in T..2 * T, ‖twistedErrorPrimePolynomial S w χ ℓ u t‖) / T) ^ 2 ≤
        C * (1 + (Z : ℝ) / T) *
          (normFiberMultiplicity (orderedConvolutionSupport S) Z : ℝ) *
          (K * Y ^ (1 - c / 2) *
            (((Fintype.card ι) ^ (Fintype.card ι) : ℕ) * (∏ i, M i)) ^ 2)) := by
  obtain ⟨K, hK, henergy⟩ := primeConvolutionError_power_energy (ι := ι)
  refine ⟨K, hK, ?_⟩
  intro S w M Y c Z hY hM hS hprod hw hYZ χ hχ ℓ u T hT
  have hprime : ∀ i, ∀ p ∈ S i, primaryPrime p := fun i p hp => (hS i p hp).1
  have hs := orderedConvolutionSupport_normNat S hprime Y Z hprod hYZ
  have hz := orderedConvolutionSupport_ne_zero S hprime
  have hf := normFiber_card_le (orderedConvolutionSupport S) Z
  have he := (coefficient_twist_energy_le (orderedConvolutionSupport S)
    (squarefreeConvolutionError S w) χ hχ).trans (henergy S w M Y c hY hM hS hprod hw)
  constructor
  · have hmean := fixedAngular_translated_dyadicMeanSquare hMV hC
      (orderedConvolutionSupport S) (fun b => squarefreeConvolutionError S w b * χ b)
      Z (normFiberMultiplicity (orderedConvolutionSupport S) Z) hs hz hf ℓ u hT
    exact hmean.trans (mul_le_mul_of_nonneg_left he (by positivity))
  · have hmean := fixedAngular_translated_meanAbsolute_sq hMV hC
      (orderedConvolutionSupport S) (fun b => squarefreeConvolutionError S w b * χ b)
      Z (normFiberMultiplicity (orderedConvolutionSupport S) Z) hs hz hf ℓ u hT
    exact hmean.trans (mul_le_mul_of_nonneg_left he (by positivity))

lemma norm_mixedCubic_le_one {q₁ q₂ : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) (b : Eisenstein) :
    ‖mixedCubic q₁ q₂ b‖ ≤ 1 := by
  rw [mixedCubic, norm_mul, norm_star]
  simpa only [mul_one] using
    mul_le_mul (norm_cubicSymbol_le_one h₁ b) (norm_cubicSymbol_le_one h₂ b)
      (_root_.norm_nonneg _) zero_le_one

/-- A mixed cubic character may be moved between the independent prime
weights and the collected convolution coefficient, even at its conductor. -/
theorem orderedConvolution_mixedCubic_weight (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {q₁ q₂ : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) (b : Eisenstein) :
    orderedConvolution S (fun i p => w i p * mixedCubic q₁ q₂ p) b =
      orderedConvolution S w b * mixedCubic q₁ q₂ b := by
  unfold orderedConvolution
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro f hf
  rw [Finset.prod_mul_distrib, ← mixedCubic_prod _ _ h₁ h₂,
    (Finset.mem_filter.mp hf).2]

/-- This is the actual squarefree mixed-character polynomial appearing
after the independent prime factors have been expanded. -/
def mixedSquarefreePrimePolynomial (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (q₁ q₂ : Eisenstein) (ℓ : ℤ) (u t : ℝ) : ℂ :=
  angularCoefficientPolynomial (orderedConvolutionSupport S)
    (fun b => squarefreeConvolution S w b * mixedCubic q₁ q₂ b) ℓ u t

theorem fullPrimeProduct_sub_mixedSquarefree (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) {q₁ q₂ : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) (ℓ : ℤ) (u t : ℝ) :
    fullPrimeProductPolynomial S (fun i p => w i p * mixedCubic q₁ q₂ p) ℓ u t -
      mixedSquarefreePrimePolynomial S w q₁ q₂ ℓ u t =
        twistedErrorPrimePolynomial S w (mixedCubic q₁ q₂) ℓ u t := by
  rw [← orderedConvolution_angular_polynomial S _ hS]
  simp only [angularCoefficientPolynomial, orderedConvolution_mixedCubic_weight S w h₁ h₂,
    mixedSquarefreePrimePolynomial, twistedErrorPrimePolynomial,
    squarefreeConvolutionError, sub_mul, Finset.sum_sub_distrib]

/-- The mixed-character twist needed by the exceptional moments satisfies
the coefficient-energy requirement without any coprimality restriction. -/
theorem mixedCubic_error_energy_le (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {q₁ q₂ : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) :
    (∑ b ∈ orderedConvolutionSupport S,
      ‖squarefreeConvolutionError S w b * mixedCubic q₁ q₂ b‖ ^ 2) ≤
        ∑ b ∈ orderedConvolutionSupport S, ‖squarefreeConvolutionError S w b‖ ^ 2 :=
  coefficient_twist_energy_le _ _ _ (fun b _ => norm_mixedCubic_le_one h₁ h₂ b)

/-- The final fixed-length specialization has no arithmetic multiplicity
hypothesis: its entire loss depends only on the number of prime factors.
In particular it applies to `mixedCubic q₁ q₂` by `norm_mixedCubic_le_one`. -/
theorem primeConvolutionError_fixedLength_height_bounds {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y c : ℝ) (Z : ℕ),
      0 < Y → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ Y ^ c < norm p) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) → Y ≤ (Z : ℝ) →
      ∀ χ : Eisenstein → ℂ,
      (∀ b ∈ orderedConvolutionSupport S, ‖χ b‖ ≤ 1) →
      ∀ (ℓ : ℤ) (u T : ℝ), 0 < T →
      (((∫ t in T..2 * T, ‖twistedErrorPrimePolynomial S w χ ℓ u t‖ ^ 2) +
        (∫ t in -2 * T..-T, ‖twistedErrorPrimePolynomial S w χ ℓ u t‖ ^ 2)) / T ≤
        2 * C * (1 + (Z : ℝ) / T) *
          ((2 * Fintype.card ι) ^ (Fintype.card ι) : ℕ) *
          (K * Y ^ (1 - c / 2) *
            (((Fintype.card ι) ^ (Fintype.card ι) : ℕ) * (∏ i, M i)) ^ 2)) ∧
      (((∫ t in T..2 * T, ‖twistedErrorPrimePolynomial S w χ ℓ u t‖) / T) ^ 2 ≤
        C * (1 + (Z : ℝ) / T) *
          ((2 * Fintype.card ι) ^ (Fintype.card ι) : ℕ) *
          (K * Y ^ (1 - c / 2) *
            (((Fintype.card ι) ^ (Fintype.card ι) : ℕ) * (∏ i, M i)) ^ 2)) := by
  obtain ⟨K, hK, hbound⟩ := primeConvolutionError_twisted_height_bounds (ι := ι) hMV hC
  refine ⟨K, hK, ?_⟩
  intro S w M Y c Z hY hM hS hprod hw hYZ χ hχ ℓ u T hT
  have h := hbound S w M Y c Z hY hM hS hprod hw hYZ χ hχ ℓ u T hT
  have hf : (normFiberMultiplicity (orderedConvolutionSupport S) Z : ℝ) ≤
      ((2 * Fintype.card ι) ^ (Fintype.card ι) : ℕ) := by
    exact_mod_cast normFiberMultiplicity_primeProducts_le S
      (fun i p hp => (hS i p hp).1) Z
  constructor
  · exact h.1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hf (by positivity)) (by positivity))
  · exact h.2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hf (by positivity)) (by positivity))

end CubicFirstMoment

end

end OAI
