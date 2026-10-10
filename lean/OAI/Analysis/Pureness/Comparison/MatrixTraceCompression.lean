import OAI.Analysis.Pureness.Comparison.MatrixCornerFunctionals

namespace OAI
noncomputable section
open scoped CStarAlgebra ComplexOrder
namespace CuntzComparison
open CuntzTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma matrixCornerProjection_norm_le (n : ℕ) : ‖matrixCornerProjection (A := A) n‖ ≤ 1 := by
  have hp := matrixCornerProjection_isStarProjection (A := A) n
  have h := CStarRing.norm_star_mul_self (x := matrixCornerProjection (A := A) n)
  rw [hp.2, hp.1] at h
  nlinarith [norm_nonneg (matrixCornerProjection (A := A) n)]

lemma matrixCornerExtract_compression (n : ℕ) (x : MatrixLimit A) :
    matrixCornerExtract n (matrixCompression n x) = matrixCornerExtract n x := by
  apply (matrixLimitStage_isometry n).injective
  rw [matrixCornerExtract_spec, matrixCompression_nested le_rfl, matrixCornerExtract_spec]

lemma TracialState.matrixCornerFunctional_compression (τ : TracialState A) (n : ℕ) (x : MatrixLimit A) :
    τ.matrixCornerFunctional n (matrixCompression n x) = τ.matrixCornerFunctional n x := by
  simp only [matrixCornerFunctional_apply, matrixCornerExtract_compression]

lemma matrixCompression_mulStar_le (n : ℕ) (x : MatrixLimit A) :
    matrixCompression n x * star (matrixCompression n x) ≤ matrixCompression n (x*star x) := by
  let q := matrixCornerProjection (A := A) n
  have hq : q*q=q := (matrixCornerProjection_isStarProjection n).1
  have hs : star q=q := (matrixCornerProjection_isStarProjection n).2
  have he : matrixCompression n x * star (matrixCompression n x) = (q*x)*q*star (q*x) := by
    rw [matrixCompression_eq_corner]
    change (q*x*q)*star (q*x*q) = _
    rw [star_mul, hs, ← mul_assoc, mul_assoc (q*x) q q, hq]
  rw [he]
  calc
    _ ≤ ‖q‖ • ((q*x)*star (q*x)) := CStarAlgebra.star_right_conjugate_le_norm_smul (q*x) q hs
    _ ≤ (1 : ℝ) • ((q*x)*star (q*x)) :=
      smul_le_smul_of_nonneg_right (matrixCornerProjection_norm_le n) (mul_star_self_nonneg (q*x))
    _ = matrixCompression n (x*star x) := by
      simp only [one_smul, star_mul, hs, matrixCompression_eq_corner, mul_assoc]
      rfl

lemma TracialState.matrixCornerFunctional_mulStar_bound (τ : TracialState A) (n : ℕ) (x : MatrixLimit A) :
    (τ.matrixCornerFunctional n (matrixCompression n x * star (matrixCompression n x))).re ≤
      (τ.matrixCornerFunctional n (x*star x)).re := by
  have h := (Complex.le_def.mp ((τ.matrixCornerFunctional n).monotone (matrixCompression_mulStar_le n x))).1
  change (τ.matrixCornerFunctional n (matrixCompression n x * star (matrixCompression n x))).re ≤
    (τ.matrixCornerFunctional n (matrixCompression n (x*star x))).re at h
  rwa [τ.matrixCornerFunctional_compression] at h
end CuntzComparison

end

end OAI
