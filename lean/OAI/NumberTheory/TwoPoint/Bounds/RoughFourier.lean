import OAI.NumberTheory.TwoPoint.PublishedInputs
import Mathlib.Analysis.Fourier.AddCircle

namespace OAI

/-!
# Exact finite Fourier identities for rough shifts

Orthogonality, convolution and the fourth moment are proved for arbitrary
finite coefficients. The sieve bounds on the number of rough integers are
not hypotheses of these identities. Haar measure on `AddCircle (1 : ℝ)` is the
ordinary integral over one period.
-/

namespace TwoPointCorrelations

open scoped BigOperators ComplexConjugate
open MeasureTheory

noncomputable def fourierPolynomial {ι : Type*} (S : Finset ι)
    (frequency : ι → ℤ) (coefficient : ι → ℂ) (θ : AddCircle (1 : ℝ)) : ℂ :=
  ∑ i ∈ S, coefficient i * fourier (frequency i) θ

theorem continuous_fourierPolynomial {ι : Type*} (S : Finset ι)
    (frequency : ι → ℤ) (coefficient : ι → ℂ) :
    Continuous (fourierPolynomial S frequency coefficient) := by
  unfold fourierPolynomial
  exact continuous_finsetSum S (fun i _ =>
    continuous_const.mul (fourier (frequency i)).continuous)

theorem integral_circle_eq_period (F : AddCircle (1 : ℝ) → ℂ) :
    (∫ θ, F θ ∂AddCircle.haarAddCircle) = ∫ x in (0 : ℝ)..1, F (x : AddCircle (1 : ℝ)) := by
  have h := fourierCoeff_eq_intervalIntegral F 0 0
  simpa only [fourierCoeff, fourier_zero, one_smul,
    neg_zero, one_div_one, zero_add] using h

theorem integral_fourier_character (n : ℤ) :
    (∫ θ : AddCircle (1 : ℝ), fourier n θ ∂AddCircle.haarAddCircle) =
      if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

theorem integrable_fourier_character (n : ℤ) :
    Integrable (fun θ : AddCircle (1 : ℝ) => fourier n θ)
      AddCircle.haarAddCircle := by
  simpa only [smul_eq_mul, mul_one] using
    (integrable_const (1 : ℂ) (μ := (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))))).fourier_smul n

theorem integral_fourierPolynomial {ι : Type*} (S : Finset ι)
    (frequency : ι → ℤ) (coefficient : ι → ℂ) :
    (∫ θ, fourierPolynomial S frequency coefficient θ ∂AddCircle.haarAddCircle) =
      ∑ i ∈ S, if frequency i = 0 then coefficient i else 0 := by
  classical
  unfold fourierPolynomial
  rw [integral_finsetSum S (fun i _ =>
    (integrable_fourier_character (frequency i)).const_mul (coefficient i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_fourier_character]
  split_ifs <;> simp_all

theorem norm_fourierPolynomial_le {ι : Type*} (S : Finset ι)
    (frequency : ι → ℤ) (coefficient : ι → ℂ) (θ : AddCircle (1 : ℝ)) :
    ‖fourierPolynomial S frequency coefficient θ‖ ≤ ∑ i ∈ S, ‖coefficient i‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one, le_refl]

theorem fourierPolynomial_mul {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (f : ι → ℤ) (g : κ → ℤ) (a : ι → ℂ) (b : κ → ℂ) (θ : AddCircle (1 : ℝ)) :
    fourierPolynomial S f a θ * fourierPolynomial T g b θ =
      fourierPolynomial (S ×ˢ T) (fun i => f i.1 + g i.2)
        (fun i => a i.1 * b i.2) θ := by
  classical
  simp only [fourierPolynomial, Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [fourier_add]
  ring

theorem fourierPolynomial_conj {ι : Type*} (S : Finset ι)
    (f : ι → ℤ) (a : ι → ℂ) (θ : AddCircle (1 : ℝ)) :
    conj (fourierPolynomial S f a θ) =
      fourierPolynomial S (fun i => -f i) (fun i => conj (a i)) θ := by
  simp only [fourierPolynomial, map_sum, map_mul, fourier_neg]

/-- Exact Fourier selection of all frequency-zero terms in a product. -/
theorem integral_fourier_product {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (f : ι → ℤ) (g : κ → ℤ) (a : ι → ℂ) (b : κ → ℂ) :
    (∫ θ, fourierPolynomial S f a θ * fourierPolynomial T g b θ
        ∂AddCircle.haarAddCircle) =
      ∑ i ∈ S ×ˢ T, if f i.1 + g i.2 = 0 then a i.1 * b i.2 else 0 := by
  simp_rw [fourierPolynomial_mul]
  exact integral_fourierPolynomial _ _ _

/-- Parseval for finite polynomials, retaining collisions of frequencies. -/
theorem integral_norm_fourierPolynomial_sq {ι : Type*} (S : Finset ι)
    (f : ι → ℤ) (a : ι → ℂ) :
    (∫ θ, ‖fourierPolynomial S f a θ‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∑ i ∈ S ×ˢ S, if f i.1 = f i.2 then (a i.1 * conj (a i.2)).re else 0 := by
  classical
  have hc : ((∫ θ, ‖fourierPolynomial S f a θ‖ ^ 2
        ∂AddCircle.haarAddCircle : ℝ) : ℂ) =
      ∑ i ∈ S ×ˢ S, if f i.1 = f i.2 then a i.1 * conj (a i.2) else 0 := by
    rw [← integral_complex_ofReal]
    simp_rw [Complex.ofReal_pow, ← Complex.mul_conj', fourierPolynomial_conj]
    rw [integral_fourier_product]
    apply Finset.sum_congr rfl
    intro i _
    simp only [add_neg_eq_zero]
  have hr := congrArg Complex.re hc
  simpa only [Complex.ofReal_re, Complex.re_sum, apply_ite, Complex.zero_re] using hr

/-- The exact weighted additive-energy identity. In particular a positive
integer dilation of the frequencies leaves its additive relation unchanged. -/
theorem integral_norm_fourierPolynomial_fourth {ι : Type*} (S : Finset ι)
    (f : ι → ℤ) (a : ι → ℂ) :
    (∫ θ, ‖fourierPolynomial S f a θ‖ ^ 4 ∂AddCircle.haarAddCircle) =
      ∑ i ∈ (S ×ˢ S) ×ˢ (S ×ˢ S),
        if f i.1.1 + f i.1.2 = f i.2.1 + f i.2.2 then
          (a i.1.1 * a i.1.2 * conj (a i.2.1 * a i.2.2)).re else 0 := by
  have h := integral_norm_fourierPolynomial_sq (S ×ˢ S)
    (fun i => f i.1 + f i.2) (fun i => a i.1 * a i.2)
  convert h using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    dsimp only
    rw [← fourierPolynomial_mul, norm_mul]
    ring

/-- The actual polynomial in `(q:rough-fourier)`. -/
noncomputable def roughFourierPolynomial (Z : Finset ℕ) (h : ℕ) : AddCircle (1 : ℝ) → ℂ :=
  fourierPolynomial Z (fun z => (h : ℤ) * z) (fun z => (z : ℂ)⁻¹)

theorem norm_roughFourierPolynomial_le (Z : Finset ℕ) (h : ℕ) (D : ℝ)
    (hD : 0 < D) (hZ : ∀ z ∈ Z, D ≤ (z : ℝ)) (θ : AddCircle (1 : ℝ)) :
    ‖roughFourierPolynomial Z h θ‖ ≤ Z.card / D := by
  apply (norm_fourierPolynomial_le Z _ _ θ).trans
  calc
    _ ≤ ∑ _z ∈ Z, D⁻¹ := by
      apply Finset.sum_le_sum
      intro z hz
      rw [norm_inv, Complex.norm_natCast]
      exact inv_anti₀ hD (hZ z hz)
    _ = _ := by simp [div_eq_mul_inv]

/-- Weighted additive energy, without any sieve hypothesis. -/
theorem roughFourierPolynomial_fourth_moment (Z : Finset ℕ) (h : ℕ) (hh : 0 < h) :
    (∫ θ, ‖roughFourierPolynomial Z h θ‖ ^ 4 ∂AddCircle.haarAddCircle) =
      ∑ i ∈ ((Z ×ˢ Z) ×ˢ (Z ×ˢ Z)).filter
          (fun i => i.1.1 + i.1.2 = i.2.1 + i.2.2),
        (i.1.1 : ℝ)⁻¹ * (i.1.2 : ℝ)⁻¹ * (i.2.1 : ℝ)⁻¹ * (i.2.2 : ℝ)⁻¹ := by
  rw [roughFourierPolynomial, integral_norm_fourierPolynomial_fourth, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have hrel : (h : ℤ) * (i.1.1 : ℤ) + (h : ℤ) * i.1.2 =
      (h : ℤ) * i.2.1 + (h : ℤ) * i.2.2 ↔ i.1.1 + i.1.2 = i.2.1 + i.2.2 := by
    rw [← mul_add, ← mul_add, mul_right_inj' (show (h : ℤ) ≠ 0 by exact_mod_cast hh.ne')]
    exact_mod_cast Iff.rfl
  simp only [hrel]
  split_ifs
  · simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.conj_ofReal, Complex.ofReal_re]
    ring
  · rfl

/-- A triple/quadruple count enters the fourth moment only through this
explicit positive weight estimate. -/
theorem roughFourierPolynomial_fourth_moment_le (Z : Finset ℕ) (h : ℕ) (hh : 0 < h)
    (D : ℝ) (hD : 0 < D) (hZ : ∀ z ∈ Z, D ≤ (z : ℝ)) :
    (∫ θ, ‖roughFourierPolynomial Z h θ‖ ^ 4 ∂AddCircle.haarAddCircle) ≤
      (((Z ×ˢ Z) ×ˢ (Z ×ˢ Z)).filter
        (fun i => i.1.1 + i.1.2 = i.2.1 + i.2.2)).card * (D⁻¹) ^ 4 := by
  rw [roughFourierPolynomial_fourth_moment Z h hh]
  calc
    _ ≤ ∑ _i ∈ ((Z ×ˢ Z) ×ˢ (Z ×ˢ Z)).filter
        (fun i => i.1.1 + i.1.2 = i.2.1 + i.2.2), (D⁻¹) ^ 4 := by
      apply Finset.sum_le_sum
      intro i hi
      have hm := Finset.mem_product.mp (Finset.mem_filter.mp hi).1
      have h₁ := inv_anti₀ hD (hZ _ (Finset.mem_product.mp hm.1).1)
      have h₂ := inv_anti₀ hD (hZ _ (Finset.mem_product.mp hm.1).2)
      have h₃ := inv_anti₀ hD (hZ _ (Finset.mem_product.mp hm.2).1)
      have h₄ := inv_anti₀ hD (hZ _ (Finset.mem_product.mp hm.2).2)
      calc
        _ ≤ D⁻¹ * D⁻¹ * D⁻¹ * D⁻¹ := by gcongr
        _ = _ := by ring
    _ = _ := by simp

end TwoPointCorrelations

end OAI
