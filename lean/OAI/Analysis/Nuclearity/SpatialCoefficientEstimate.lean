import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace OAI

/-! The elementary coefficient estimate used to pass from almost central
Hilbert--Schmidt vectors to spatial tensor functionals. No multiplicativity
of a completely positive map is inferred from centrality. -/

noncomputable section
open scoped InnerProductSpace ComplexStarModule

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma norm_inner_left_difference_le (z : H) (L : H →L[ℂ] H) (x y : H) :
    ‖inner ℂ z (L x) - inner ℂ z (L y)‖ ≤ ‖z‖ * (‖L‖ * ‖x - y‖) := by
  rw [← inner_sub_right, ← map_sub]
  exact (norm_inner_le_norm z (L (x - y))).trans
    (mul_le_mul_of_nonneg_left (L.le_opNorm (x - y)) (norm_nonneg z))

lemma norm_inner_unit_left_difference_le (z : H) (hz : ‖z‖ = 1)
    (L : H →L[ℂ] H) (x y : H) :
    ‖inner ℂ z (L x) - inner ℂ z (L y)‖ ≤ ‖L‖ * ‖x - y‖ := by
  simpa only [hz, one_mul] using norm_inner_left_difference_le z L x y

/-- The product coefficient error separates into the actual vector
intertwining error and the single-operator state error. -/
lemma norm_product_coefficient_error_le (z : H) (hz : ‖z‖ = 1)
    (L R S : H →L[ℂ] H) (α : ℂ) :
    ‖inner ℂ z ((L * R) z) - α‖ ≤
      ‖L‖ * ‖R z - S z‖ + ‖inner ℂ z ((L * S) z) - α‖ := by
  calc
    ‖inner ℂ z ((L * R) z) - α‖ ≤
        ‖inner ℂ z ((L * R) z) - inner ℂ z ((L * S) z)‖ +
          ‖inner ℂ z ((L * S) z) - α‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖L‖ * ‖R z - S z‖ + ‖inner ℂ z ((L * S) z) - α‖ :=
      add_le_add (norm_inner_unit_left_difference_le z hz L (R z) (S z)) le_rfl

lemma norm_sum_product_coefficient_error_le {ι : Type*} [Fintype ι]
    (z : H) (hz : ‖z‖ = 1) (L R S : ι → H →L[ℂ] H) (α : ι → ℂ) :
    ‖(∑ i, inner ℂ z ((L i * R i) z)) - ∑ i, α i‖ ≤
      ∑ i, (‖L i‖ * ‖R i z - S i z‖ +
        ‖inner ℂ z ((L i * S i) z) - α i‖) := by
  rw [← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    norm_product_coefficient_error_le z hz (L i) (R i) (S i) (α i))

section RealImaginary

variable [CompleteSpace H]

lemma realPart_operator_coefficient (T : H →L[ℂ] H) (z : H) :
    (inner ℂ z ((ℜ T : H →L[ℂ] H) z)).re = (inner ℂ z (T z)).re := by
  have hs : (inner ℂ z ((star T) z)).re = (inner ℂ z (T z)).re := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact inner_re_symm (𝕜 := ℂ) (T z) z
  rw [realPart_apply_coe]
  simp only [smul_apply, add_apply, inner_smul_right_eq_smul, inner_add_right,
    Complex.smul_re, Complex.add_re, smul_eq_mul, hs]
  ring

lemma imaginaryPart_operator_coefficient (T : H →L[ℂ] H) (z : H) :
    (inner ℂ z ((ℑ T : H →L[ℂ] H) z)).re = (inner ℂ z (T z)).im := by
  have hs : inner ℂ z ((star T) z) = star (inner ℂ z (T z)) := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact (inner_conj_symm (T z) z).symm
  rw [imaginaryPart_apply_coe]
  simp only [smul_apply, sub_apply, inner_smul_right_eq_smul, inner_sub_right,
    smul_eq_mul, hs, Complex.star_def]
  simp [Complex.mul_re, Complex.mul_im]
  have him : (inner ℂ (T z) z).im = -(inner ℂ z (T z)).im :=
    inner_im_symm (𝕜 := ℂ) (T z) z
  rw [him]
  ring

variable {A : Type*} [SeminormedAddCommGroup A] [NormedSpace ℂ A]
  [StarAddMonoid A] [StarModule ℂ A]

/-- Real and imaginary self-adjoint tests control the complex state value. -/
lemma complex_coefficient_error_le (f : A →ₗ[ℂ] ℂ)
    (hf : ∀ a, f (star a) = star (f a))
    (π : A →ₗ[ℂ] (H →L[ℂ] H)) (hπ : ∀ a, π (star a) = star (π a))
    (a : A) (z : H) :
    ‖f a - inner ℂ z (π a z)‖ ≤
      |(f (ℜ a)).re - (inner ℂ z (π (ℜ a) z)).re| +
      |(f (ℑ a)).re - (inner ℂ z (π (ℑ a) z)).re| := by
  have hfr : (f (ℜ a)).re = (f a).re := by
    rw [realPart_apply_coe]
    simp only [f.map_smul_of_tower, map_add, hf, Complex.smul_re, Complex.add_re,
      smul_eq_mul, Complex.star_def, Complex.conj_re]
    ring
  have hfi : (f (ℑ a)).re = (f a).im := by
    rw [imaginaryPart_apply_coe]
    simp only [f.map_smul_of_tower, map_sub, hf, smul_eq_mul,
      Complex.star_def]
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hpr : π (ℜ a) = (ℜ (π a) : H →L[ℂ] H) := by
    simp only [realPart_apply_coe, π.map_smul_of_tower, map_add, hπ]
  have hpi : π (ℑ a) = (ℑ (π a) : H →L[ℂ] H) := by
    simp only [imaginaryPart_apply_coe, π.map_smul_of_tower, map_sub, hπ]
  rw [hfr, hfi, hpr, hpi, realPart_operator_coefficient, imaginaryPart_operator_coefficient]
  simpa only [Complex.sub_re, Complex.sub_im] using
    Complex.norm_le_abs_re_add_abs_im (f a - inner ℂ z (π a z))

end RealImaginary

end WeakPureInfiniteness

end

end OAI
