import OAI.Analysis.KadisonKastler.TomiyamaPositive
import OAI.Analysis.KadisonKastler.TomiyamaCornerGeometry
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI

/-! # The projection part of Tomiyama's theorem

A unital contractive retraction onto a C-star subalgebra respects left
and right multiplication by projections in that subalgebra.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

local instance tomiyamaProjectionSourceOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance tomiyamaProjectionSourceStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance tomiyamaProjectionTargetOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance tomiyamaProjectionTargetStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

variable (φ : B →⋆ₐ[ℂ] A) (P : A →L[ℂ] B)
  (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (hfix : ∀ b, P (φ b) = b)

include hfix in
private theorem tomiyama_map_one : P 1 = 1 := by
  simpa only [map_one] using hfix 1

include hP hfix

private theorem tomiyama_mono {x y : A} (hxy : x ≤ y) : P x ≤ P y := by
  rw [← sub_nonneg, ← map_sub]
  exact unital_contraction_nonneg P hP (tomiyama_map_one φ P hfix) _ (sub_nonneg.mpr hxy)

/-- Positivity ensures that the image of a diagonal corner stays in that
corner. -/
theorem tomiyama_corner_supported (e : B) (he : IsStarProjection e) (x : A) :
    e * P (φ e * x * φ e) * e = P (φ e * x * φ e) := by
  have hbasic (x : A) (hx : 0 ≤ x) (hxn : ‖x‖ ≤ 1) :
      e * P (φ e * x * φ e) * e = P (φ e * x * φ e) := by
    have heφ := he.map φ
    have hpos : 0 ≤ φ e * x * φ e := by
      simpa only [heφ.isSelfAdjoint.star_eq] using star_left_conjugate_nonneg hx (φ e)
    have hupper : φ e * x * φ e ≤ φ e := by
      have ht := heφ.isSelfAdjoint.conjugate_le_conjugate
        ((CStarAlgebra.norm_le_one_iff_of_nonneg x hx).mp hxn)
      simpa only [mul_one, heφ.isIdempotentElem.eq] using ht
    have himg : 0 ≤ P (φ e * x * φ e) :=
      unital_contraction_nonneg P hP (tomiyama_map_one φ P hfix) _ hpos
    have hi : P (φ e * x * φ e) ≤ e := by
      simpa only [hfix] using tomiyama_mono φ P hP hfix hupper
    exact he.conjugate_of_nonneg_of_le himg hi
  have hx : x ∈ Submodule.span ℂ ({a : A | 0 ≤ a} ∩ Metric.closedBall 0 1) := by
    rw [CStarAlgebra.span_nonneg_inter_unitClosedBall]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact hbasic y hy.1 (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy.2)
  | zero => simp only [mul_zero, zero_mul, map_zero]
  | add y z hy hz hiy hiz =>
    simp only [mul_add, add_mul, map_add, hiy, hiz]
  | smul c y hy hiy =>
    simp only [mul_smul_comm, smul_mul_assoc, map_smul, hiy]

private theorem tomiyama_compressed_zero_of_bounds (e : B) (he : IsStarProjection e)
    (z : A) (C : ℝ)
    (hb : ∀ t : ℝ, ‖φ e + t • z‖ ^ 2 ≤ 1 + C * t ^ 2)
    (hi : ∀ t : ℝ, ‖φ e + t • (Complex.I • z)‖ ^ 2 ≤ 1 + C * t ^ 2) :
    e * P z * e = 0 := by
  have hbound (a : A) (t : ℝ) :
      ‖e + t • (e * P a * e)‖ ≤ ‖φ e + t • a‖ := by
    calc
      ‖e + t • (e * P a * e)‖ = ‖e * P (φ e + t • a) * e‖ := by
        rw [map_add, P.map_smul_of_tower, hfix, mul_add, add_mul,
          mul_smul_comm, smul_mul_assoc, he.isIdempotentElem.eq,
          he.isIdempotentElem.eq]
      _ ≤ ‖P (φ e + t • a)‖ := norm_projection_compression_le e _ he
      _ ≤ ‖φ e + t • a‖ := hP _
  apply corner_eq_zero_of_quadratic_bounds e _ he
    (by rw [← mul_assoc, ← mul_assoc, he.isIdempotentElem.eq])
    (by simp only [mul_assoc, he.isIdempotentElem.eq]) C
  · intro t
    exact (pow_le_pow_left₀ (norm_nonneg _) (hbound z t) 2).trans (hb t)
  · intro t
    have hn := hbound (Complex.I • z) t
    simp only [map_smul, mul_smul_comm, smul_mul_assoc] at hn
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (hi t)

/-- A source block orthogonal on the right has zero diagonal image. -/
theorem tomiyama_compressed_zero_of_mul_right_zero (e : B) (he : IsStarProjection e)
    (z : A) (hz : z * φ e = 0) : e * P z * e = 0 := by
  apply tomiyama_compressed_zero_of_bounds φ P hP hfix e he z (‖z‖ ^ 2)
  · exact norm_projection_add_sq_le (φ e) z (he.map φ) hz
  · intro t
    have hi : (Complex.I • z) * φ e = 0 := by rw [smul_mul_assoc, hz, smul_zero]
    simpa only [norm_smul, Complex.norm_I, one_mul] using
      norm_projection_add_sq_le (φ e) (Complex.I • z) (he.map φ) hi t

/-- The analogous statement for a source block orthogonal on the left. -/
theorem tomiyama_compressed_zero_of_mul_left_zero (e : B) (he : IsStarProjection e)
    (z : A) (hz : φ e * z = 0) : e * P z * e = 0 := by
  apply tomiyama_compressed_zero_of_bounds φ P hP hfix e he z (‖z‖ ^ 2)
  · exact norm_projection_add_sq_le' (φ e) z (he.map φ) hz
  · intro t
    have hi : φ e * (Complex.I • z) = 0 := by rw [mul_smul_comm, hz, smul_zero]
    simpa only [norm_smul, Complex.norm_I, one_mul] using
      norm_projection_add_sq_le' (φ e) (Complex.I • z) (he.map φ) hi t

end

end KadisonKastler

end OAI
