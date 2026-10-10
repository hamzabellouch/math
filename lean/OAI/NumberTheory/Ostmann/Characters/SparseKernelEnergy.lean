import OAI.NumberTheory.Ostmann.Characters.SparseAdditiveKernel
import OAI.NumberTheory.Ostmann.Characters.GaussFourier

namespace OAI

/-! # Energy bounds for the sparse kernel and its pointwise square -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def rawAdditiveKernelAction {p : ℕ} [NeZero p]
    (k f : ZMod p → ℂ) (x : ZMod p) : ℂ := ∑ y, f y * k (x - y)

theorem rawAdditiveKernelAction_fourier {p : ℕ} [NeZero p]
    (k f : ZMod p → ℂ) (a : ZMod p) :
    densityFourier (rawAdditiveKernelAction k f) a =
      ((p : ℂ) * additiveFourier k a) * densityFourier f a := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have he : rawAdditiveKernelAction k f = fun x => (p : ℂ) * additiveConvolution f k x := by
    funext x
    simp only [rawAdditiveKernelAction, additiveConvolution, ← mul_assoc,
      mul_inv_cancel₀ hp, one_mul]
  rw [he, densityFourier, additiveFourier_const_mul, additiveFourier_convolution]
  unfold densityFourier
  ring

theorem rawAdditiveKernelAction_energy_le {p : ℕ} [NeZero p]
    (k f : ZMod p → ℂ) (B : ℝ)
    (hk : ∀ a, ‖(p : ℂ) * additiveFourier k a‖ ≤ B) :
    (∑ x, ‖rawAdditiveKernelAction k f x‖ ^ 2) ≤ B ^ 2 * ∑ x, ‖f x‖ ^ 2 := by
  rw [← densityFourier_energy, ← densityFourier_energy f, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [rawAdditiveKernelAction_fourier, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (hk a) 2) (sq_nonneg _)

theorem sparseAdditiveKernel_square_fourier {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t : ℝ) (a : ZMod p) :
    additiveFourier (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) a =
      (t : ℂ) ^ 2 * ((p : ℂ)⁻¹) ^ 2 * ((E.filter fun b => a - b ∈ E).card : ℂ) := by
  rw [additiveFourier_pointwise_mul]
  simp_rw [sparseAdditiveKernel_fourier]
  have he (b : ZMod p) :
      ((t : ℂ) * (p : ℂ)⁻¹ * (if b ∈ E then 1 else 0)) *
        ((t : ℂ) * (p : ℂ)⁻¹ * (if a - b ∈ E then 1 else 0)) =
      ((t : ℂ) ^ 2 * ((p : ℂ)⁻¹) ^ 2) *
        (if b ∈ E ∧ a - b ∈ E then 1 else 0) := by
    split_ifs <;> simp_all
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  congr 1
  simp [← Finset.filter_filter]

/-- Equation (5.8): the square kernel has raw operator norm at most
`t^2 epsilon`. The estimate retains the actual convolution multiplicities. -/
theorem sparseAdditiveKernel_square_multiplier_le {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t ε : ℝ) (hE : (E.card : ℝ) ≤ ε * p) (a : ZMod p) :
    ‖(p : ℂ) * additiveFourier
      (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) a‖ ≤ t ^ 2 * ε := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hc : ((E.filter fun b => a - b ∈ E).card : ℝ) ≤ ε * p := by
    have hc' : ((E.filter fun b => a - b ∈ E).card : ℝ) ≤ E.card := by
      exact_mod_cast Finset.card_filter_le E (fun b => a - b ∈ E)
    exact hc'.trans hE
  rw [sparseAdditiveKernel_square_fourier]
  simp only [norm_mul, norm_pow, norm_inv, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  have he : (p : ℝ) * (t ^ 2 * ((p : ℝ)⁻¹) ^ 2 *
      ((E.filter fun b => a - b ∈ E).card : ℝ)) =
      t ^ 2 * (((E.filter fun b => a - b ∈ E).card : ℝ) / p) := by
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hp).mpr hc) (sq_nonneg _)

theorem sparseAdditiveKernel_square_energy_le {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (t ε : ℝ) (hE : (E.card : ℝ) ≤ ε * p)
    (f : ZMod p → ℂ) :
    (∑ x, ‖rawAdditiveKernelAction
      (fun x => sparseAdditiveKernel E t x * sparseAdditiveKernel E t x) f x‖ ^ 2) ≤
      (t ^ 2 * ε) ^ 2 * ∑ x, ‖f x‖ ^ 2 :=
  rawAdditiveKernelAction_energy_le _ _ _
    (sparseAdditiveKernel_square_multiplier_le E t ε hE)

end Ostmann

end OAI
