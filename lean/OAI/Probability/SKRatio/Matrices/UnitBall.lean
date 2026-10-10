import Mathlib
import OAI.Probability.SKRatio.Matrices.GaussianQuadraticSupComparison
import OAI.Probability.SKRatio.Matrices.GaussianAffineGaussianSup
import OAI.Probability.SKRatio.Matrices.DiagonalSqrt
import OAI.Probability.SKRatio.Matrices.GaussianQuadratic

namespace OAI

section
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
namespace SKRatioGaussian
lemma quadratic_interpolation {z q v c : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hc : 0 ≤ c) (hqc : q*v ≤ c) {X : ℝ} (hX : X - q*v ≤ c) :
    z*X-z^2*q*v ≤ c := by
  have h1 := mul_le_mul_of_nonneg_left hX hz0
  have h2 := mul_le_mul_of_nonneg_left hqc (mul_nonneg hz0 (sub_nonneg.mpr hz1))
  have h3 := mul_nonneg hc (sq_nonneg (1-z))
  nlinarith only [h1, h2, h3]

section DiagonalProcess
variable {ι : Type*} [Fintype ι]

abbrev UnitBall (ι : Type*) [Fintype ι] :=
  ↥(Metric.closedBall (0 : EuclideanSpace ℝ ι) 1)

instance : Nonempty (UnitBall ι) := ⟨⟨0, by simp⟩⟩

lemma norm_UnitBall_le (p : UnitBall ι) : ‖(p : EuclideanSpace ℝ ι)‖ ≤ 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using p.property

def diagonalOffset (a : ι → ℝ) (z q : ℝ) (p : UnitBall ι) : ℝ :=
  -z^2 * q * ‖diagonalSqrt a p‖^2

def diagonalProcess (r : ℝ) (a : ι → ℝ) (z q : ℝ)
    (g : MatrixCoordinates ι → ℝ) : ℝ :=
  gaussianSup (diagonalOffset a z q)
    (fun p k => z * quadraticCoeff r (diagonalSqrt a p) k) g

def diagonalLinearProcess (r : ℝ) (a : ι → ℝ) (z q : ℝ)
    (g : MatrixCoordinates ι → ℝ) : ℝ :=
  gaussianSup (diagonalOffset a z q)
    (fun p k => z * linearCoeff r (diagonalSqrt a p) k) g

def diagonalWeights (r : ℝ) (a : ι → ℝ) : MatrixCoordinates ι → ℝ
  | Sum.inl _ => 0
  | Sum.inr i => r * a i

def diagonalT (r : ℝ) (a : ι → ℝ) (g : MatrixCoordinates ι → ℝ) : ℝ :=
  sqrt (gaussianQuadratic (diagonalWeights r a) g)

lemma continuous_diagonalOffset (a : ι → ℝ) (z q : ℝ) :
    Continuous (diagonalOffset a z q) := by
  exact continuous_const.mul (((continuous_diagonalSqrt a).comp continuous_subtype_val).norm.pow 2)

lemma continuous_diagonalCoeff {f : EuclideanSpace ℝ ι → MatrixCoordinates ι → ℝ}
    (hf : Continuous f) (a : ι → ℝ) (z : ℝ) :
    Continuous (fun p : UnitBall ι => fun k => z * f (diagonalSqrt a p) k) := by
  apply continuous_pi
  intro k
  exact continuous_const.mul ((continuous_apply k).comp
    (hf.comp ((continuous_diagonalSqrt a).comp continuous_subtype_val)))

lemma integrable_diagonalProcess (r : ℝ) (a : ι → ℝ) (z q : ℝ) :
    Integrable (diagonalProcess r a z q) (gaussianCoordinates (MatrixCoordinates ι)) :=
  integrable_gaussianSup (continuous_diagonalOffset a z q)
    (continuous_diagonalCoeff (continuous_quadraticCoeff r) a z)

lemma integrable_diagonalLinearProcess (r : ℝ) (a : ι → ℝ) (z q : ℝ) :
    Integrable (diagonalLinearProcess r a z q) (gaussianCoordinates (MatrixCoordinates ι)) :=
  integrable_gaussianSup (continuous_diagonalOffset a z q)
    (continuous_diagonalCoeff (continuous_linearCoeff r) a z)

lemma diagonalT_norm {r : ℝ} (hr : 0 ≤ r) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (g : MatrixCoordinates ι → ℝ) :
    diagonalT r a g = sqrt r * ‖diagonalSqrt a (WithLp.toLp 2 (fun i => g (.inr i)))‖ := by
  unfold diagonalT gaussianQuadratic
  rw [Fintype.sum_sum_type]
  simp only [diagonalWeights, zero_mul, Finset.sum_const_zero, zero_add]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, Real.sqrt_mul hr]
  have he := diagonalSqrt_norm_sq a ha (WithLp.toLp 2 (fun i => g (.inr i)))
  rw [← he, Real.sqrt_sq (norm_nonneg _)]

lemma diagonalWeights_sum (r : ℝ) (a : ι → ℝ) :
    (∑ k, diagonalWeights r a k) = r * ∑ i, a i := by
  simp only [Fintype.sum_sum_type, diagonalWeights, Finset.sum_const_zero, zero_add,
    Finset.mul_sum]

lemma diagonalWeights_sum_sq (r : ℝ) (a : ι → ℝ) :
    (∑ k, (diagonalWeights r a k)^2) = r^2 * ∑ i, (a i)^2 := by
  simp only [Fintype.sum_sum_type, diagonalWeights, zero_pow (by norm_num : (2:ℕ)≠0),
    Finset.sum_const_zero, zero_add, mul_pow, Finset.mul_sum]

lemma diagonalT_integrable {r : ℝ} (hr : 0 ≤ r) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    Integrable (diagonalT r a) (gaussianCoordinates (MatrixCoordinates ι)) := by
  apply (memLp_sqrt_of_nonneg ((gaussianQuadratic_memLp (diagonalWeights r a)).integrable
    (by norm_num)) ?_).integrable (by norm_num)
  intro g
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg _ (sq_nonneg _)
  cases k <;> simp only [diagonalWeights]
  · exact le_rfl
  · exact mul_nonneg hr (ha _)

lemma diagonalT_fluctuation {r : ℝ} (hr : 0 ≤ r) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    (∫ g, |diagonalT r a g - sqrt (r * ∑ i, a i)|
      ∂gaussianCoordinates (MatrixCoordinates ι)) ≤
      sqrt (sqrt (2*r^2 * ∑ i, (a i)^2)) := by
  have hp (g) : 0 ≤ gaussianQuadratic (diagonalWeights r a) g := by
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg _ (sq_nonneg _)
    cases k <;> simp only [diagonalWeights]
    · exact le_rfl
    · exact mul_nonneg hr (ha _)
  have h := integral_sqrt_fluctuation (gaussianQuadratic_memLp (diagonalWeights r a)) hp
  rw [gaussianQuadratic_mean, gaussianQuadratic_variance,
    diagonalWeights_sum, diagonalWeights_sum_sq, ← mul_assoc] at h
  exact h

lemma diagonalLinearProcess_le {r z q A b : ℝ} {a : ι → ℝ}
    (hr : 0 ≤ r) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hq : 0 ≤ q)
    (hqb : sqrt q * sqrt A ≤ b) (hb : b ≤ 1)
    (g : MatrixCoordinates ι → ℝ) :
    diagonalLinearProcess r a z q g ≤
      1-(1-b)^2 + 2 * sqrt A * |diagonalT r a g - sqrt q| := by
  unfold diagonalLinearProcess
  apply gaussianSup_le (continuous_diagonalOffset a z q)
    (continuous_diagonalCoeff (continuous_linearCoeff r) a z)
  intro p
  let w := diagonalSqrt a p
  let v := ‖w‖
  have hv0 : 0 ≤ v := norm_nonneg _
  have hv : v ≤ sqrt A := diagonalSqrt_norm_le_sqrt ha hA0 hA (norm_UnitBall_le p)
  have hdot := diagonal_sum_mul_le_norm a (p : EuclideanSpace ℝ ι)
    (WithLp.toLp 2 (fun i => g (.inr i)))
  have hdot' : (∑ i, w i * g (.inr i)) ≤
      ‖diagonalSqrt a (WithLp.toLp 2 (fun i => g (.inr i)))‖ :=
    hdot.trans ((mul_le_mul_of_nonneg_right (norm_UnitBall_le p) (norm_nonneg _)).trans_eq
      (one_mul _))
  have hcoeff : (∑ k, (z * linearCoeff r w k) * g k) =
      2*z*sqrt r*v * (∑ i, w i * g (.inr i)) := by
    simp only [Fintype.sum_sum_type, linearCoeff, mul_zero, zero_mul,
      Finset.sum_const_zero, zero_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [v]
    ring
  have hlin := mul_le_mul_of_nonneg_left hdot' (show 0 ≤ 2*z*sqrt r*v by positivity)
  have hT := diagonalT_norm hr ha g
  have hlin' : (∑ k, (z * linearCoeff r w k) * g k) ≤ 2*z*v*diagonalT r a g := by
    rw [hcoeff, hT]
    nlinarith only [hlin]
  have hd0 : 0 ≤ z * sqrt q * v := by positivity
  have hzb : z * sqrt q * v ≤ b := by
    calc
      _ ≤ sqrt q * v := by nlinarith [mul_nonneg (sqrt_nonneg q) hv0]
      _ ≤ sqrt q * sqrt A := mul_le_mul_of_nonneg_left hv (sqrt_nonneg q)
      _ ≤ b := hqb
  have hmargin := quadratic_margin hd0 hzb hb
  have hs := sq_sqrt hq
  have hab := le_abs_self (diagonalT r a g - sqrt q)
  have hvz : z*v ≤ sqrt A := (mul_le_of_le_one_left hv0 hz1).trans hv
  have herr : 2*z*v*(diagonalT r a g - sqrt q) ≤
      2*sqrt A*|diagonalT r a g - sqrt q| := by
    exact (mul_le_mul_of_nonneg_left hab (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg _))
  change -z^2*q*v^2 + (∑ k, (z * linearCoeff r w k) * g k) ≤ _
  nlinarith only [hlin', hmargin, herr, hs, sq_nonneg (z*v)]

theorem diagonalProcess_expected_margin [Nonempty ι]
    {r z A b : ℝ} {a : ι → ℝ}
    (hr : 0 ≤ r) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hqb : sqrt (r * ∑ i, a i) * sqrt A ≤ b) (hb : b ≤ 1) :
    (∫ g, diagonalProcess r a z (r * ∑ i, a i) g
      ∂gaussianCoordinates (MatrixCoordinates ι)) ≤
      1-(1-b)^2 + 2*sqrt A * sqrt (sqrt (2*r^2 * ∑ i, (a i)^2)) := by
  let q := r * ∑ i, a i
  have hq : 0 ≤ q := mul_nonneg hr (Finset.sum_nonneg (fun i _ => ha i))
  have hcomp := gaussian_quadraticSup_comparison
    (continuous_diagonalOffset a z q)
    ((continuous_diagonalSqrt a).comp continuous_subtype_val) hr z
  have hfluct := diagonalT_fluctuation hr ha
  have hi : Integrable (fun g => |diagonalT r a g - sqrt q|)
      (gaussianCoordinates (MatrixCoordinates ι)) :=
    ((diagonalT_integrable hr ha).sub (integrable_const _)).abs
  have hbound : (∫ g, diagonalLinearProcess r a z q g
      ∂gaussianCoordinates (MatrixCoordinates ι)) ≤
      1-(1-b)^2 + 2*sqrt A *
        (∫ g, |diagonalT r a g - sqrt q| ∂gaussianCoordinates (MatrixCoordinates ι)) := by
    calc
      _ ≤ ∫ g, (1-(1-b)^2 + 2*sqrt A*|diagonalT r a g - sqrt q|)
          ∂gaussianCoordinates (MatrixCoordinates ι) :=
        integral_mono (integrable_diagonalLinearProcess r a z q)
          ((integrable_const _).add (hi.const_mul _))
          (diagonalLinearProcess_le hr ha hA hA0 hz0 hz1 hq hqb hb)
      _ = _ := by rw [integral_add (integrable_const _) (hi.const_mul _),
                      integral_const, probReal_univ, one_smul, integral_const_mul]
  exact hcomp.trans (hbound.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hfluct (show 0 ≤ 2*sqrt A by positivity))))

lemma diagonalProcess_lipschitz {r z A : ℝ} {a : ι → ℝ}
    (hr : 0 ≤ r) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A)
    (hz : 0 ≤ z) (q : ℝ) :
    LipschitzWith (Real.toNNReal (z * sqrt (2*r) * A))
      (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) =>
        diagonalProcess r a z q g.ofLp) := by
  apply gaussianSup_lipschitz (continuous_diagonalOffset a z q)
    (continuous_diagonalCoeff (continuous_quadraticCoeff r) a z)
  intro p
  have hsq := diagonalSqrt_norm_sq_le ha hA (p : EuclideanSpace ℝ ι)
  have hp2 : ‖(p : EuclideanSpace ℝ ι)‖^2 ≤ 1 := by
    nlinarith [norm_UnitBall_le p, norm_nonneg (p : EuclideanSpace ℝ ι)]
  have hw : ‖diagonalSqrt a p‖^2 ≤ A :=
    hsq.trans ((mul_le_mul_of_nonneg_left hp2 hA0).trans_eq (mul_one A))
  have he : WithLp.toLp 2 (fun k => z * quadraticCoeff r (diagonalSqrt a p) k) =
      z • WithLp.toLp 2 (quadraticCoeff r (diagonalSqrt a p)) := rfl
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hz, quadraticCoeff_norm hr,
    Real.toNNReal_of_nonneg (by positivity)]
  simpa only [mul_assoc, NNReal.coe_mk] using
    mul_le_mul_of_nonneg_left hw (show 0 ≤ z * sqrt (2*r) by positivity)

theorem diagonalProcess_path_le {r A q c : ℝ} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hA0 : 0 ≤ A)
    (hq : 0 ≤ q) (hc : 0 ≤ c) (hqc : q*A ≤ c)
    {g : MatrixCoordinates ι → ℝ} (hg : diagonalProcess r a 1 q g ≤ c)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    diagonalProcess r a z q g ≤ c := by
  apply gaussianSup_le (continuous_diagonalOffset a z q)
    (continuous_diagonalCoeff (continuous_quadraticCoeff r) a z)
  intro p
  let w := diagonalSqrt a p
  let v := ‖w‖^2
  let X := ∑ k, quadraticCoeff r w k * g k
  have hp2 : ‖(p : EuclideanSpace ℝ ι)‖^2 ≤ 1 := by
    nlinarith [norm_UnitBall_le p, norm_nonneg (p : EuclideanSpace ℝ ι)]
  have hv : v ≤ A := (diagonalSqrt_norm_sq_le ha hA _).trans
    ((mul_le_mul_of_nonneg_left hp2 hA0).trans_eq (mul_one A))
  have hqv : q*v ≤ c := (mul_le_mul_of_nonneg_left hv hq).trans hqc
  have hX : X - q*v ≤ c := by
    have h := (gaussianAffine_le_gaussianSup (continuous_diagonalOffset a 1 q)
      (continuous_diagonalCoeff (continuous_quadraticCoeff r) a 1) g p).trans hg
    simp only [gaussianAffine, diagonalOffset, one_mul, one_pow, neg_mul] at h
    simpa only [sub_eq_add_neg, add_comm, X, v, w] using h
  have h := quadratic_interpolation hz0 hz1 hc hqv hX
  convert h using 1
  simp only [gaussianAffine, diagonalOffset, X, v, w, Finset.mul_sum]
  simp_rw [mul_assoc]
  ring

end DiagonalProcess
end SKRatioGaussian

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
