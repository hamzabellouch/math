import Mathlib
import OAI.Probability.SKGap.Localization.DiagonalTMemLp

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def matrixQuad (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, ∑ k, p i * M i k * p k

def matrixOperator (M : Matrix ι ι ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  M.toEuclideanLin.toContinuousLinearMap

lemma matrixOperator_apply (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) (i : ι) :
    matrixOperator M p i = ∑ k, M i k * p k := by
  rfl

lemma matrixQuad_inner (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) :
    matrixQuad M p = inner ℝ p (matrixOperator M p) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, matrixOperator_apply,
    matrixQuad, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq ι] in
lemma matrixQuad_smul (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) (c : ℝ) :
    matrixQuad M (c • p) = c^2 * matrixQuad M p := by
  simp only [matrixQuad, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma goeMatrix_symm (r : ℝ) (g : MatrixCoordinates ι → ℝ) :
    (goeMatrix r g).IsHermitian := by
  ext i k
  simp [goeMatrix, add_comm]

omit [Fintype ι] [DecidableEq ι] in
lemma goeMatrix_neg (r : ℝ) (g : MatrixCoordinates ι → ℝ) :
    goeMatrix r (-g) = -goeMatrix r g := by
  ext i k
  simp only [goeMatrix, Pi.neg_apply, Matrix.neg_apply]
  ring

omit [DecidableEq ι] in
lemma goeMatrix_quad (r : ℝ) (g : MatrixCoordinates ι → ℝ) (p : EuclideanSpace ℝ ι) :
    matrixQuad (goeMatrix r g) p =
      ∑ i, ∑ k, sqrt (2*r) * p i * p k * g (.inl (i,k)) := by
  have hs : (∑ i, ∑ k, p i * g (.inl (k,i)) * p k) =
      ∑ i, ∑ k, p i * g (.inl (i,k)) * p k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    _ = sqrt (2*r)/2 * ((∑ i, ∑ k, p i * g (.inl (i,k)) * p k) +
        ∑ i, ∑ k, p i * g (.inl (k,i)) * p k) := by
      simp only [matrixQuad, goeMatrix, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [hs]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring

lemma matrixOperator_norm_le_of_quad {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    {R : ℝ} (hR : 0 ≤ R)
    (hq : ∀ p : EuclideanSpace ℝ ι, ‖p‖ ≤ 1 → |matrixQuad M p| ≤ R) :
    ‖matrixOperator M‖ ≤ R := by
  have hs : (matrixOperator M).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient (T := matrixOperator M) hs]
  apply ciSup_le
  intro p
  by_cases hp : p = 0
  · simp [hp, ContinuousLinearMap.rayleighQuotient, hR]
  have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hunit : ‖‖p‖⁻¹ • p‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp0, inv_mul_cancel₀ hp0.ne']
  have hh := hq (‖p‖⁻¹ • p) hunit
  rw [matrixQuad_smul, abs_mul, abs_pow, abs_inv, abs_of_pos hp0] at hh
  simpa only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real, real_inner_comm, ← matrixQuad_inner, abs_div,
    abs_pow, abs_of_pos hp0, inv_pow, div_eq_mul_inv, mul_comm, abs_mul, abs_inv] using hh

end SKGap

namespace SKGap
section GOEEvents
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
lemma goeMatrix_quad_coeff (r : ℝ) (g : MatrixCoordinates ι → ℝ)
    (p : EuclideanSpace ℝ ι) :
    matrixQuad (goeMatrix r g) p = ∑ k, quadraticCoeff r p k * g k := by
  rw [goeMatrix_quad, Fintype.sum_sum_type]
  simp only [quadraticCoeff, zero_mul, Finset.sum_const_zero, add_zero,
    Fintype.sum_prod_type]

omit [DecidableEq ι] [Nonempty ι] in
lemma diagonal_affine_matrix (r z q : ℝ) (a : ι → ℝ)
    (g : MatrixCoordinates ι → ℝ) (p : UnitBall ι) :
    gaussianAffine (diagonalOffset a z q)
      (fun p k => z * quadraticCoeff r (diagonalSqrt a p) k) g p =
        z * matrixQuad (goeMatrix r g) (diagonalSqrt a p) -
          z^2*q*‖diagonalSqrt a p‖^2 := by
  rw [goeMatrix_quad_coeff]
  simp only [gaussianAffine, diagonalOffset, Finset.mul_sum]
  simp_rw [mul_assoc]
  ring

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma diagonalSqrt_one (p : EuclideanSpace ℝ ι) :
    diagonalSqrt (fun _ : ι => 1) p = p := by
  ext i
  simp [diagonalSqrt]

omit [DecidableEq ι] [Nonempty ι] in
lemma goe_quad_le_top (r : ℝ) (g : MatrixCoordinates ι → ℝ)
    (p : EuclideanSpace ℝ ι) (hp : ‖p‖ ≤ 1) :
    matrixQuad (goeMatrix r g) p ≤ diagonalProcess r (fun _ : ι => 1) 1 0 g := by
  let p' : UnitBall ι := ⟨p, by simpa only [Metric.mem_closedBall, dist_zero_right] using hp⟩
  have h := gaussianAffine_le_gaussianSup (continuous_diagonalOffset (fun _ : ι => 1) 1 0)
    (continuous_diagonalCoeff (continuous_quadraticCoeff r) (fun _ : ι => 1) 1) g p'
  rw [diagonal_affine_matrix, diagonalSqrt_one] at h
  simpa only [one_mul, mul_zero, zero_mul, sub_zero, diagonalProcess, p'] using h

omit [DecidableEq ι] [Nonempty ι] in
lemma matrixQuad_neg (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) :
    matrixQuad (-M) p = -matrixQuad M p := by
  simp [matrixQuad, Finset.sum_neg_distrib]

omit [Nonempty ι] in
lemma goe_norm_le_of_top {r R : ℝ} (hR : 0 ≤ R) (g : MatrixCoordinates ι → ℝ)
    (hpos : diagonalProcess r (fun _ : ι => 1) 1 0 g ≤ R)
    (hneg : diagonalProcess r (fun _ : ι => 1) 1 0 (-g) ≤ R) :
    ‖matrixOperator (goeMatrix r g)‖ ≤ R := by
  apply matrixOperator_norm_le_of_quad (goeMatrix_symm r g) hR
  intro p hp
  apply abs_le.mpr
  constructor
  · have h := (goe_quad_le_top r (-g) p hp).trans hneg
    rw [goeMatrix_neg, matrixQuad_neg] at h
    linarith
  · exact (goe_quad_le_top r g p hp).trans hpos

theorem goe_norm_tail {j ε : ℝ} (hj : 0 < j) (hε : 0 ≤ ε) :
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | 2*sqrt j+ε < ‖matrixOperator (goeMatrix (j/(Fintype.card ι:ℝ)) g)‖} ≤
      2*Real.exp (-ε^2*(Fintype.card ι:ℝ)/(π^2*j)) := by
  let r := j/(Fintype.card ι:ℝ)
  let R := 2*sqrt j+ε
  let P := diagonalProcess r (fun _ : ι => 1) 1 0
  let E : Set (MatrixCoordinates ι → ℝ) := {g | R < P g}
  have hc : Continuous P := continuous_gaussianSup
    (continuous_diagonalOffset (fun _ : ι => 1) 1 0)
    (continuous_diagonalCoeff (continuous_quadraticCoeff r) (fun _ : ι => 1) 1)
  have hm : MeasurableSet E := measurableSet_lt measurable_const hc.measurable
  have hp := goe_top_tail (ι := ι) hj hε
  have hn : (gaussianCoordinates (MatrixCoordinates ι)).real {g | R < P (-g)} =
      (gaussianCoordinates (MatrixCoordinates ι)).real E := by
    exact congrArg ENNReal.toReal (gaussianCoordinates_preserving_neg.measure_preimage hm.nullMeasurableSet)
  have hs : {g : MatrixCoordinates ι → ℝ | R < ‖matrixOperator (goeMatrix r g)‖} ⊆ E ∪ {g | R < P (-g)} := by
    intro g hg
    by_contra hh
    have hh' : ¬ R < P g ∧ ¬ R < P (-g) := by simpa only [Set.mem_union, E, Set.mem_ofPred_eq, not_or] using hh
    exact (not_lt_of_ge (goe_norm_le_of_top (by dsimp [R]; positivity) g
      (le_of_not_gt hh'.1) (le_of_not_gt hh'.2))) hg
  calc
    _ ≤ (gaussianCoordinates (MatrixCoordinates ι)).real (E ∪ {g | R < P (-g)}) := measureReal_mono hs
    _ ≤ (gaussianCoordinates (MatrixCoordinates ι)).real E +
        (gaussianCoordinates (MatrixCoordinates ι)).real {g | R < P (-g)} := measureReal_union_le _ _
    _ = 2*(gaussianCoordinates (MatrixCoordinates ι)).real E := by rw [hn]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)

end GOEEvents
end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
