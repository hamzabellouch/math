import OAI.Geometry.Immersion.ClosedSurface.PhaseMean

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean
open Set


def covectorSquare (ξ : Base) : PhaseMean.Tensor := ![ξ.1 ^ 2, ξ.1 * ξ.2, ξ.2 ^ 2]


def basisCoefficient (t u v : ℝ) : PhaseMean.Tensor →L[ℝ] ℝ :=
  (((t - u) * (t - v))⁻¹) •
    ((ContinuousLinearMap.proj 2 : PhaseMean.Tensor →L[ℝ] ℝ) -
      (u + v) • ContinuousLinearMap.proj 1 + (u * v) • ContinuousLinearMap.proj 0)

lemma basisCoefficient_apply (t u v : ℝ) (H : PhaseMean.Tensor) :
    basisCoefficient t u v H = (H 2 - (u + v) * H 1 + u * v * H 0) / ((t - u) * (t - v)) := by
  simp only [basisCoefficient, smul_apply, add_apply,
    sub_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, div_eq_mul_inv]
  ring

lemma covectorSquare_smul (w : ℝ) (ξ : Base) :
    covectorSquare (w • ξ) = w ^ 2 • covectorSquare ξ := by
  ext i
  fin_cases i <;> simp [covectorSquare, smul_eq_mul] <;> ring



lemma three_slope_decomposition {t₀ t₁ t₂ : ℝ} (h₀₁ : t₀ ≠ t₁)
    (h₀₂ : t₀ ≠ t₂) (h₁₂ : t₁ ≠ t₂) (H : PhaseMean.Tensor) :
    basisCoefficient t₀ t₁ t₂ H • covectorSquare (1, t₀) +
      basisCoefficient t₁ t₀ t₂ H • covectorSquare (1, t₁) +
      basisCoefficient t₂ t₀ t₁ H • covectorSquare (1, t₂) = H := by
  have h10 : t₁ - t₀ ≠ 0 := sub_ne_zero.mpr h₀₁.symm
  have h20 : t₂ - t₀ ≠ 0 := sub_ne_zero.mpr h₀₂.symm
  have h21 : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr h₁₂.symm
  have h01 : t₀ - t₁ ≠ 0 := sub_ne_zero.mpr h₀₁
  have h02 : t₀ - t₂ ≠ 0 := sub_ne_zero.mpr h₀₂
  have h12 : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h₁₂
  ext i
  fin_cases i <;>
    simp [Pi.add_apply, basisCoefficient_apply, covectorSquare] <;>
    field_simp [h10, h20, h21, h01, h02, h12] <;> ring



lemma normalized_numerators_positive {x₀ x₁ x₂ : ℝ}
    (h₀ : x₀ ∈ Ioo (-3 : ℝ) (-2)) (h₁ : x₁ ∈ Ioo (-(1/4) : ℝ) (1/4))
    (h₂ : x₂ ∈ Ioo (2 : ℝ) 3) :
    0 < 1 + x₁*x₂ ∧ 1 + x₀*x₂ < 0 ∧ 0 < 1 + x₀*x₁ := by
  have hx₂ : 0 < x₂ := by linarith [h₂.1]
  have hx₀ : 0 < -x₀ := by linarith [h₀.2]
  have hp₁ := mul_pos (show 0 < x₁ + 1/4 by linarith [h₁.1]) hx₂
  have hp₂ := mul_pos (show 0 < -x₀ - 2 by linarith [h₀.2]) hx₂
  have hp₃ := mul_pos (show 0 < 1/4 - x₁ by linarith [h₁.2]) hx₀
  constructor
  · nlinarith [h₂.2]
  constructor
  · nlinarith [h₂.1]
  · nlinarith [h₀.1]

lemma positive_center_parameters {H : PhaseMean.Tensor} (h₀ : 0 < H 0)
    (hdet : 0 < H 0 * H 2 - (H 1) ^ 2) :
    ∃ β r : ℝ, 0 < r ∧ H 1 = H 0 * β ∧ H 2 = H 0 * (β ^ 2 + r ^ 2) := by
  let β := H 1 / H 0
  let D := H 2 / H 0 - β ^ 2
  have hD : 0 < D := by
    have he : D = (H 0 * H 2 - (H 1) ^ 2) / (H 0) ^ 2 := by
      dsimp [D, β]
      field_simp
    rw [he]
    exact div_pos hdet (sq_pos_of_pos h₀)
  refine ⟨β, Real.sqrt D, Real.sqrt_pos.2 hD, ?_, ?_⟩
  · dsimp [β]
    field_simp
  · rw [Real.sq_sqrt hD.le]
    dsimp [D]
    field_simp
    ring

lemma shifted_numerator (H : PhaseMean.Tensor) {β r : ℝ}
    (h₁ : H 1 = H 0 * β) (h₂ : H 2 = H 0 * (β ^ 2 + r ^ 2)) (u v : ℝ) :
    H 2 - ((β + r*u) + (β + r*v)) * H 1 + (β + r*u)*(β + r*v)*H 0 =
      H 0 * r ^ 2 * (1 + u*v) := by
  rw [h₁, h₂]
  ring

lemma shifted_basis_positive {H : PhaseMean.Tensor} (h₀ : 0 < H 0)
    {β r x₀ x₁ x₂ : ℝ} (hr : 0 < r)
    (h₁ : H 1 = H 0 * β) (h₂ : H 2 = H 0 * (β ^ 2 + r ^ 2))
    (hx₀ : x₀ ∈ Ioo (-3 : ℝ) (-2)) (hx₁ : x₁ ∈ Ioo (-(1/4) : ℝ) (1/4))
    (hx₂ : x₂ ∈ Ioo (2 : ℝ) 3) :
    0 < basisCoefficient (β+r*x₀) (β+r*x₁) (β+r*x₂) H ∧
    0 < basisCoefficient (β+r*x₁) (β+r*x₀) (β+r*x₂) H ∧
    0 < basisCoefficient (β+r*x₂) (β+r*x₀) (β+r*x₁) H := by
  have hnum := normalized_numerators_positive hx₀ hx₁ hx₂
  have h01 : β+r*x₀ < β+r*x₁ := by nlinarith [hx₀.2, hx₁.1]
  have h12 : β+r*x₁ < β+r*x₂ := by nlinarith [hx₁.2, hx₂.1]
  have hp : 0 < H 0 * r ^ 2 := mul_pos h₀ (sq_pos_of_pos hr)
  simp only [basisCoefficient_apply, shifted_numerator H h₁ h₂]
  refine ⟨div_pos (mul_pos hp hnum.1) (mul_pos_of_neg_of_neg (sub_neg.mpr h01)
    (sub_neg.mpr (h01.trans h12))), ?_, ?_⟩
  · exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hp hnum.2.1)
      (mul_neg_of_pos_of_neg (sub_pos.mpr h01) (sub_neg.mpr h12))
  · exact div_pos (mul_pos hp hnum.2.2)
      (mul_pos (sub_pos.mpr (h01.trans h12)) (sub_pos.mpr h12))

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
