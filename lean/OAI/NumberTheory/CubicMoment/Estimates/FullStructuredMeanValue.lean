import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeConvolution
import OAI.NumberTheory.CubicMoment.Estimates.StructuredMeanValue
import OAI.NumberTheory.CubicMoment.Estimates.StructuredCoefficientEnergy

namespace OAI

/-! The ordinary published mean-value theorem applied to the literal
prime convolution, with every numerator and excluded-prime factor retained. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_prime (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    ∀ i, ∀ z ∈ fullPrimeSupport R W X i, primaryPrime z := by
  intro i z hz
  exact ⟨(mem_primaryElementBall.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1,
    (Finset.mem_filter.mp hz).2⟩

lemma fullPrimeSupport_eq_product_cutoff {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 1 ≤ X i)
    (hhi : ∀ i x, R < x → W i x = 0) :
    fullPrimeSupport R W X = coordinatePrimeSupport W X (R/2*(∏ i, X i)) := by
  apply fullPrimeSupport_eq_coordinate W X (fun i => zero_lt_one.trans_le (hX i)) hhi
  intro i
  have h := mul_le_mul_of_nonneg_left (coordinate_le_product X hX i) hR
  nlinarith

def fullStructuredAngularSum (R : ℝ) (h v e : Eisenstein) (ℓ : ℤ) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (fullPrimeSupport R W X)).filter (fun z => IsCoprime z e),
    fullPrimeCoefficient R W X z*cubicSymbol z (v*h)*theta ℓ z*mellinPhase u (norm z)

lemma fullStructuredAngularSum_zero (R : ℝ) (h v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    fullStructuredAngularSum R h v e 0 u W X = fullStructuredPrimeSum R h 1 v e u W X := by
  unfold fullStructuredAngularSum fullStructuredPrimeSum
  apply Finset.sum_congr rfl
  intro z _
  simp only [theta_zero,mul_one,one_pow]
  ring

def fullStructuredCoefficient (R : ℝ) (h v e : Eisenstein)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (z : Eisenstein) : ℂ :=
  if IsCoprime z e then fullPrimeCoefficient R W X z*cubicSymbol z (v*h) else 0

lemma fullStructuredAngularSum_eq (R : ℝ) (h v e : Eisenstein) (ℓ : ℤ) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    fullStructuredAngularSum R h v e ℓ u W X =
      ∑ z ∈ orderedConvolutionSupport (fullPrimeSupport R W X),
        fullStructuredCoefficient R h v e W X z*theta ℓ z*mellinPhase u (norm z) := by
  unfold fullStructuredAngularSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  unfold fullStructuredCoefficient
  split_ifs <;> simp only [zero_mul]

lemma fullStructuredCoefficient_energy_le (R : ℝ) (h v e : Eisenstein)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    (∑ z ∈ orderedConvolutionSupport (fullPrimeSupport R W X),
      ‖fullStructuredCoefficient R h v e W X z‖^2) ≤
    ∑ z ∈ orderedConvolutionSupport (fullPrimeSupport R W X),
      ‖fullPrimeCoefficient R W X z‖^2 := by
  apply Finset.sum_le_sum
  intro z hz
  have hp := orderedPrimarySupport_primary (fullPrimeSupport R W X)
    (fun i p hp => (fullPrimeSupport_prime R W X i p hp).1) hz
  apply pow_le_pow_left₀ (_root_.norm_nonneg (fullStructuredCoefficient R h v e W X z)) _ 2
  unfold fullStructuredCoefficient
  split_ifs
  · rw [norm_mul]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hp _)
  · simpa only [norm_zero] using _root_.norm_nonneg (fullPrimeCoefficient R W X z)

theorem fullStructured_dyadicMeanSquare {C R : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 1 ≤ X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (Z : ℕ) (hZ : R^(Fintype.card ι)*(∏ i, X i) ≤ (Z:ℝ))
    (h v e : Eisenstein) (ℓ : ℤ) (u : ℝ) {T : ℝ} (hT : 0 < T) :
    ((∫ t in T..2*T, ‖fullStructuredAngularSum R h v e ℓ (t+u) W X‖^2) +
     (∫ t in -2*T..-T, ‖fullStructuredAngularSum R h v e ℓ (t+u) W X‖^2))/T ≤
      2*C*(1+(Z:ℝ)/T)*((2*Fintype.card ι)^(Fintype.card ι):ℕ)*
        ∑ z ∈ orderedConvolutionSupport (fullPrimeSupport R W X),
          ‖fullPrimeCoefficient R W X z‖^2 := by
  let S := fullPrimeSupport R W X
  have hprime : ∀ i, ∀ z ∈ S i, primaryPrime z := fullPrimeSupport_prime R W X
  have hnorm : ∀ z ∈ orderedConvolutionSupport S,
      norm z ≤ R^(Fintype.card ι)*(∏ i, X i) := by
    rw [show S = coordinatePrimeSupport W X (R/2*(∏ i, X i)) from
      fullPrimeSupport_eq_product_cutoff hR W X hX hhi]
    exact fun z hz => (coordinatePrimeProduct_norm_bounds W X
      (fun i => zero_lt_one.trans_le (hX i)) hR hlo hhi _ z hz).2
  have hprod : ∀ f ∈ Fintype.piFinset S,
      norm (∏ i, f i) ≤ R^(Fintype.card ι)*(∏ i, X i) := by
    intro f hf
    exact hnorm _ (Finset.mem_image.mpr ⟨f,hf,rfl⟩)
  have hmult : ∀ n ∈ Finset.Icc 1 Z,
      (((orderedConvolutionSupport S).filter (fun b => normNat b = n)).card:ℝ) ≤
        ((2*Fintype.card ι)^(Fintype.card ι):ℕ) := by
    intro n hn
    exact (normFiber_card_le _ Z n hn).trans
      (by exact_mod_cast normFiberMultiplicity_primeProducts_le S hprime Z)
  simp_rw [fullStructuredAngularSum_eq]
  have hb := fixedAngular_translated_dyadicMeanSquare hMV hC
    (orderedConvolutionSupport S) (fullStructuredCoefficient R h v e W X) Z
    ((2*Fintype.card ι)^(Fintype.card ι):ℕ)
    (orderedConvolutionSupport_normNat S hprime _ Z hprod hZ)
    (orderedConvolutionSupport_ne_zero S hprime) hmult ℓ u hT
  apply hb.trans
  exact mul_le_mul_of_nonneg_left (fullStructuredCoefficient_energy_le R h v e W X)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC)
      (by positivity)) (Nat.cast_nonneg _))

end CubicFirstMoment

end

end OAI
