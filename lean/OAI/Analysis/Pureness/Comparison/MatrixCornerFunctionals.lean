import OAI.Analysis.Pureness.Stabilization.MatrixPositive
import OAI.Analysis.Pureness.Comparison.MatrixUnitCorners
import OAI.Analysis.Pureness.Comparison.PositiveReflection
import OAI.Analysis.Pureness.Comparison.TracialExtendedTrace

namespace OAI
noncomputable section
open scoped CStarAlgebra ComplexOrder ENNReal Topology
namespace CuntzComparison
open CuntzTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma matrixCornerExtract_continuous (n : ℕ) : Continuous (matrixCornerExtract (A := A) n) := by
  let L : MatrixLimit A →L[ℂ] FinMatrix A n :=
    (matrixCornerExtractLinear n).mkContinuous 1 (fun x => by simpa only [matrixCornerExtractLinear, LinearMap.coe_mk, AddHom.coe_mk, one_mul] using matrixCornerExtract_norm_le n x)
  exact L.continuous

lemma matrixCornerExtract_nonneg (n : ℕ) {x : MatrixLimit A} (hx : 0 ≤ x) :
    0 ≤ matrixCornerExtract n x := by
  apply nonneg_of_injective_starHom (matrixLimitStage n) (matrixLimitStage_isometry n).injective
  rw [matrixCornerExtract_spec, matrixCompression_eq_corner]
  have hs : star (matrixCornerProjection (A := A) n) = matrixCornerProjection n :=
    (matrixCornerProjection_isStarProjection n).2
  simpa only [hs] using star_left_conjugate_nonneg hx (matrixCornerProjection (A := A) n)

lemma matrixCornerProjection_mul {n m : ℕ} (h : n ≤ m) :
    matrixCornerProjection (A := A) n * matrixCornerProjection m = matrixCornerProjection n := by
  change matrixLimitStage n 1 * matrixLimitStage m 1 = matrixLimitStage n 1
  rw [← matrixLimitStage_compatible h 1, ← map_mul, mul_one]

lemma matrixCornerProjection_mul_rev {n m : ℕ} (h : n ≤ m) :
    matrixCornerProjection (A := A) m * matrixCornerProjection n = matrixCornerProjection n := by
  change matrixLimitStage m 1 * matrixLimitStage n 1 = matrixLimitStage n 1
  rw [← matrixLimitStage_compatible h 1, ← map_mul, one_mul]

lemma matrixCompression_nested {n m : ℕ} (h : n ≤ m) (x : MatrixLimit A) :
    matrixCompression n (matrixCompression m x) = matrixCompression n x := by
  simp only [matrixCompression_eq_corner]
  rw [← mul_assoc (matrixCornerProjection n) (matrixCornerProjection m * x),
    ← mul_assoc (matrixCornerProjection n) (matrixCornerProjection m), matrixCornerProjection_mul h,
    mul_assoc (matrixCornerProjection n * x), matrixCornerProjection_mul_rev h]

lemma matrixCornerExtract_stage_large {n m : ℕ} (h : m ≤ n) (M : FinMatrix A m) :
    matrixCornerExtract n (matrixLimitStage m M) = matrixInclusion h M := by
  apply (matrixLimitStage_isometry n).injective
  rw [matrixCornerExtract_spec, matrixCompression_stage, matrixMask_eq_self h,
    matrixLimitStage_compatible]

lemma matrixCornerExtract_stage_small {n m : ℕ} (h : n ≤ m) (M : FinMatrix A m) :
    matrixCornerExtract n (matrixLimitStage m M) = matrixRestrict h M := by
  apply (matrixLimitStage_isometry n).injective
  rw [matrixCornerExtract_spec, matrixCompression_stage, ← matrixInclusion_restrict h M,
    matrixLimitStage_compatible]

lemma matrixCornerExtract_coherent {n m : ℕ} (h : n ≤ m) (x : MatrixLimit A) :
    matrixRestrict h (matrixCornerExtract m x) = matrixCornerExtract n x := by
  rw [← matrixCornerExtract_stage_small h, matrixCornerExtract_spec]
  apply (matrixLimitStage_isometry n).injective
  rw [matrixCornerExtract_spec, matrixCompression_nested h, matrixCornerExtract_spec]

def TracialState.matrixCornerFunctional (τ : TracialState A) (n : ℕ) : MatrixLimit A →ₚ[ℂ] ℂ where
  toLinearMap := τ.matrixTraceLinear.comp (matrixCornerExtractLinear n)
  monotone' x y h := by
    apply sub_nonneg.mp
    change 0 ≤ τ.matrixTraceLinear (matrixCornerExtract n y) - τ.matrixTraceLinear (matrixCornerExtract n x)
    rw [← map_sub]
    change 0 ≤ τ.matrixTraceLinear (matrixCornerExtractLinear n y - matrixCornerExtractLinear n x)
    rw [← map_sub]
    exact τ.matrixTrace_nonneg (matrixCornerExtract_nonneg n (sub_nonneg.mpr h))

@[simp] lemma TracialState.matrixCornerFunctional_apply (τ : TracialState A) (n : ℕ) (x : MatrixLimit A) :
    τ.matrixCornerFunctional n x = τ.matrixTraceLinear (matrixCornerExtract n x) := rfl

theorem TracialState.matrixCornerFunctional_monotone (τ : TracialState A) {x : MatrixLimit A} (hx : 0 ≤ x) :
    Monotone (fun n => (τ.matrixCornerFunctional n x).re) := by
  apply monotone_nat_of_le_succ
  intro n
  let M := matrixCornerExtract (n+1) x
  have hm := matrixCornerExtract_nonneg (n+1) hx
  have he := matrixCornerExtract_coherent (Nat.le_succ n) x
  change (τ.matrixTraceLinear (matrixCornerExtract n x)).re ≤ (τ.matrixTraceLinear M).re
  rw [← he]
  simp only [TracialState.matrixTraceLinear, LinearMap.coe_mk, AddHom.coe_mk, Complex.re_sum,
    Fin.sum_univ_castSucc, Complex.add_re, Complex.re_sum, matrixRestrict]
  change (∑ i : Fin n, (τ.toPositiveLinearMap (M i.castSucc i.castSucc)).re) ≤
    (∑ i : Fin n, (τ.toPositiveLinearMap (M i.castSucc i.castSucc)).re) +
      (τ.toPositiveLinearMap (M (Fin.last n) (Fin.last n))).re
  exact le_add_of_nonneg_right (Complex.nonneg_iff.mp
    (τ.toPositiveLinearMap.map_nonneg (Positive.matrix_diagonal_nonneg ⟨M,hm⟩ (Fin.last n)))).1
end CuntzComparison

end

end OAI
