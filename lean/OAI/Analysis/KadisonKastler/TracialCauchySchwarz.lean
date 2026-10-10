import OAI.Analysis.KadisonKastler.BoundedSequence
import Mathlib.Analysis.InnerProductSpace.Defs

namespace OAI

/-!
# Cauchy–Schwarz for the faithful tracial two-norm

The imaginary-part condition on positive squares gives the Hermitian
symmetry of the trace pairing by polarization. The existing algebraic
inner-product core then supplies Cauchy–Schwarz, without changing the
ambient C*-algebra norm.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

/-- Polarization of real positive-square values makes the trace
pairing Hermitian. -/
theorem FaithfulTracialState.star_pair_symm (τ : FaithfulTracialState B) (x y : B) :
    star (τ.toLinearMap (star y * x)) = τ.toLinearMap (star x * y) := by
  have hadd := τ.positive_im (x + y)
  simp only [star_add, add_mul, mul_add, map_add, Complex.add_im,
    τ.positive_im, zero_add, add_zero] at hadd
  have hI := τ.positive_im (x + Complex.I • y)
  simp [star_smul, add_mul, mul_add,
    Complex.mul_re, Complex.mul_im, τ.positive_im] at hI
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]
    linarith
  · simp only [Complex.star_def, Complex.conj_im]
    linarith

/-- A positive complex-linear trace commutes with the involution. -/
theorem FaithfulTracialState.map_star (τ : FaithfulTracialState B) (x : B) :
    τ.toLinearMap (star x) = star (τ.toLinearMap x) := by
  simpa only [star_one, one_mul, mul_one] using (τ.star_pair_symm x 1).symm

@[instance_reducible]
private def tracialInnerCore (τ : FaithfulTracialState B) :
    PreInnerProductSpace.Core ℂ B where
  inner x y := τ.toLinearMap (star x * y)
  conj_inner_symm x y := by
    change star (τ.toLinearMap (star y * x)) = τ.toLinearMap (star x * y)
    exact τ.star_pair_symm x y
  re_inner_nonneg x := τ.positive x
  add_left x y z := by simp [star_add, add_mul]
  smul_left x y c := by
    change τ.toLinearMap (star (c • x) * y) = star c * τ.toLinearMap (star x * y)
    simp [star_smul]

/-- The tracial two-norm is nonnegative. -/
theorem traceTwoNorm_nonneg (τ : FaithfulTracialState B) (x : B) :
    0 ≤ traceTwoNorm τ x := Real.sqrt_nonneg _

/-- Its square is the real positive-square trace. -/
theorem traceTwoNorm_sq (τ : FaithfulTracialState B) (x : B) :
    traceTwoNorm τ x ^ 2 = (τ.toLinearMap (star x * x)).re :=
  Real.sq_sqrt (τ.positive x)

@[simp]
theorem traceTwoNorm_one (τ : FaithfulTracialState B) : traceTwoNorm τ (1 : B) = 1 := by
  simp [traceTwoNorm, τ.map_one]

@[simp]
theorem traceTwoNorm_star (τ : FaithfulTracialState B) (x : B) :
    traceTwoNorm τ (star x) = traceTwoNorm τ x := by
  simp only [traceTwoNorm, star_star, τ.tracial x (star x)]

/-- Cauchy–Schwarz for the complex trace pairing. -/
theorem FaithfulTracialState.cauchySchwarz (τ : FaithfulTracialState B) (x y : B) :
    ‖τ.toLinearMap (star x * y)‖ ≤ traceTwoNorm τ x * traceTwoNorm τ y := by
  let : PreInnerProductSpace.Core ℂ B := tracialInnerCore τ
  have hc := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) x y
  change ‖τ.toLinearMap (star x * y)‖ * ‖τ.toLinearMap (star y * x)‖ ≤
    (τ.toLinearMap (star x * x)).re * (τ.toLinearMap (star y * y)).re at hc
  have hn : ‖τ.toLinearMap (star y * x)‖ = ‖τ.toLinearMap (star x * y)‖ := by
    rw [← norm_star (τ.toLinearMap (star y * x)), τ.star_pair_symm x y]
  rw [hn] at hc
  have hs : ‖τ.toLinearMap (star x * y)‖ ^ 2 ≤
      (traceTwoNorm τ x * traceTwoNorm τ y) ^ 2 := by
    rw [mul_pow, traceTwoNorm_sq, traceTwoNorm_sq, pow_two]
    exact hc
  have hp := mul_nonneg (traceTwoNorm_nonneg τ x) (traceTwoNorm_nonneg τ y)
  nlinarith [norm_nonneg (τ.toLinearMap (star x * y))]

/-- Cauchy–Schwarz with the identity bounds a trace by the two-norm. -/
theorem FaithfulTracialState.norm_apply_le_traceTwoNorm (τ : FaithfulTracialState B) (x : B) :
    ‖τ.toLinearMap x‖ ≤ traceTwoNorm τ x := by
  simpa only [star_one, one_mul, traceTwoNorm_one] using τ.cauchySchwarz 1 x

/-- The tracial two-norm satisfies the triangle inequality. -/
theorem traceTwoNorm_add_le (τ : FaithfulTracialState B) (x y : B) :
    traceTwoNorm τ (x + y) ≤ traceTwoNorm τ x + traceTwoNorm τ y := by
  have hxy : (τ.toLinearMap (star x * y)).re ≤ traceTwoNorm τ x * traceTwoNorm τ y :=
    (Complex.re_le_norm _).trans (τ.cauchySchwarz x y)
  have hyx : (τ.toLinearMap (star y * x)).re ≤ traceTwoNorm τ x * traceTwoNorm τ y := by
    simpa only [mul_comm] using (Complex.re_le_norm _).trans (τ.cauchySchwarz y x)
  have he : (τ.toLinearMap (star (x + y) * (x + y))).re =
      (τ.toLinearMap (star x * x)).re + (τ.toLinearMap (star x * y)).re +
        (τ.toLinearMap (star y * x)).re + (τ.toLinearMap (star y * y)).re := by
    simp only [star_add, add_mul, mul_add, map_add, Complex.add_re]
    ring
  have hsum := traceTwoNorm_sq τ (x + y)
  rw [he] at hsum
  have hx := traceTwoNorm_sq τ x
  have hy := traceTwoNorm_sq τ y
  have hn := traceTwoNorm_nonneg τ (x + y)
  have hnx := traceTwoNorm_nonneg τ x
  have hny := traceTwoNorm_nonneg τ y
  nlinarith

/-- The tracial two-norm is dominated by the original operator norm. -/
theorem traceTwoNorm_le_norm (τ : FaithfulTracialState B) (x : B) :
    traceTwoNorm τ x ≤ ‖x‖ := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hpos : 0 ≤ algebraMap ℝ B (‖x‖ ^ 2) - star x * x :=
    sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq x)
  obtain ⟨z, hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos
  have hscalar : τ.toLinearMap (algebraMap ℝ B (‖x‖ ^ 2)) =
      Complex.ofReal (‖x‖ ^ 2) := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, τ.map_one]
    simp
  have ht := τ.positive z
  rw [← hz, map_sub, hscalar, Complex.sub_re, Complex.ofReal_re] at ht
  have hs := traceTwoNorm_sq τ x
  have hn := traceTwoNorm_nonneg τ x
  nlinarith [norm_nonneg x]

/-- In particular, the normalized positive trace is a contraction. -/
theorem FaithfulTracialState.norm_apply_le_norm (τ : FaithfulTracialState B) (x : B) :
    ‖τ.toLinearMap x‖ ≤ ‖x‖ :=
  (τ.norm_apply_le_traceTwoNorm x).trans (traceTwoNorm_le_norm τ x)

end

end KadisonKastler

end OAI
