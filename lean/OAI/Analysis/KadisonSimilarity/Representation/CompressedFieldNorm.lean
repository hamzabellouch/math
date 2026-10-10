import OAI.Analysis.KadisonSimilarity.Representation.ProjectionFieldReduction
import OAI.Analysis.KadisonSimilarity.Tracial.IsometricMatrixExtension

namespace OAI

/-! Exact scalar and matrix norms after restricting actual zero-extension
fields to the fibers of the range projection. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {H F Ω : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  (J : H →ₗᵢ[ℂ] Lp F 2 μ)
  (p : Ω → F →L[ℂ] F) (hp : ∀ x, IsStarProjection (p x))
  (hP : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J 1 f x = p x (f x))

include hP

theorem ae_isometric_field_left_support
    (T : H →L[ℂ] H) (R : Ω → F →L[ℂ] F)
    (hR : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J T f x = R x (f x)) :
    ∀ᵐ x ∂μ, p x * R x = R x := by
  apply ae_field_left_support μ _ _ p R hP hR
  rw [← isometricExtension_mul, one_mul]

theorem ae_isometric_field_right_support
    (T : H →L[ℂ] H) (R : Ω → F →L[ℂ] F)
    (hR : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J T f x = R x (f x)) :
    ∀ᵐ x ∂μ, R x * p x = R x := by
  apply ae_field_right_support μ _ _ p R hP hR
  rw [← isometricExtension_mul, mul_one]

theorem norm_le_iff_compressed_field
    (T : H →L[ℂ] H) (R : Ω → F →L[ℂ] F)
    (hR : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J T f x = R x (f x))
    (C : ℝ) (hC : 0 ≤ C) :
    ‖T‖ ≤ C ↔ ∀ᵐ x ∂μ, ‖projectionFiberCompression (p x) (hp x) (R x)‖ ≤ C := by
  have hn := pointwise_field_norm_iff μ (isometricExtension J T) R hR C hC
  rw [isometricExtension_norm] at hn
  have hc : ∀ᵐ x ∂μ, ‖projectionFiberCompression (p x) (hp x) (R x)‖ = ‖R x‖ := by
    filter_upwards [ae_isometric_field_left_support μ J p hP T R hR,
      ae_isometric_field_right_support μ J p hP T R hR] with x hl hr
    exact norm_projectionFiberCompression (p x) (hp x) (R x) hl hr
  constructor
  · intro h
    filter_upwards [hn.mp h, hc] with x hx he
    exact he.le.trans hx
  · intro h
    apply hn.mpr
    filter_upwards [h, hc] with x hx he
    exact he.symm.le.trans hx

theorem matrix_norm_le_iff_compressed_field {n : ℕ}
    (T : Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (R : Matrix (Fin n) (Fin n) (Ω → F →L[ℂ] F))
    (hR : ∀ i j (f : Lp F 2 μ), ∀ᵐ x ∂μ,
      isometricExtension J (T i j) f x = R i j x (f x))
    (C : ℝ) (hC : 0 ≤ C) :
    ‖matrixOperator T‖ ≤ C ↔ ∀ᵐ x ∂μ,
      ‖matrixOperator (fun i j => projectionFiberCompression (p x) (hp x) (R i j x))‖ ≤ C := by
  have hn := diagonal_matrix_norm_iff μ (fun i j => isometricExtension J (T i j))
    (fun x i j => R i j x) hR C hC
  rw [norm_matrix_isometricExtension] at hn
  have hl : ∀ᵐ x ∂μ, ∀ i j, p x * R i j x = R i j x :=
    eventually_countable_forall.mpr fun i => eventually_countable_forall.mpr fun j =>
      ae_isometric_field_left_support μ J p hP (T i j) (R i j) (hR i j)
  have hr : ∀ᵐ x ∂μ, ∀ i j, R i j x * p x = R i j x :=
    eventually_countable_forall.mpr fun i => eventually_countable_forall.mpr fun j =>
      ae_isometric_field_right_support μ J p hP (T i j) (R i j) (hR i j)
  have hc : ∀ᵐ x ∂μ,
      ‖matrixOperator (fun i j => projectionFiberCompression (p x) (hp x) (R i j x))‖ =
        ‖matrixOperator (fun i j => R i j x)‖ := by
    filter_upwards [hl, hr] with x hleft hright
    exact norm_matrix_projectionFiberCompression (p x) (hp x) (fun i j => R i j x) hleft hright
  constructor
  · intro h
    filter_upwards [hn.mp h, hc] with x hx he
    exact he.le.trans hx
  · intro h
    apply hn.mpr
    filter_upwards [h, hc] with x hx he
    exact he.symm.le.trans hx

end KadisonSimilarity

end

end OAI
