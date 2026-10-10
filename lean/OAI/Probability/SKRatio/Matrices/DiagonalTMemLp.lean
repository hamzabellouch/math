import Mathlib
import OAI.Probability.SKRatio.Matrices.UnitBall
import OAI.Probability.SKRatio.Matrices.GaussianProductUpperTailLipschitz

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
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKRatioGaussian
section GOEProbability
variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma diagonalT_memLp {r : ℝ} (hr : 0 ≤ r) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    MemLp (diagonalT r a) 2 (gaussianCoordinates (MatrixCoordinates ι)) := by
  apply memLp_sqrt_of_nonneg ((gaussianQuadratic_memLp (diagonalWeights r a)).integrable
    (by norm_num))
  intro g
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg _ (sq_nonneg _)
  cases k <;> simp only [diagonalWeights]
  · exact le_rfl
  · exact mul_nonneg hr (ha _)

omit [Nonempty ι] in
lemma diagonalT_mean_le {r : ℝ} (hr : 0 ≤ r) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    (∫ g, diagonalT r a g ∂gaussianCoordinates (MatrixCoordinates ι)) ≤
      sqrt (r * ∑ i, a i) := by
  have he (g : MatrixCoordinates ι → ℝ) : (diagonalT r a g)^2 =
      gaussianQuadratic (diagonalWeights r a) g := by
    apply sq_sqrt
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg _ (sq_nonneg _)
    cases k <;> simp only [diagonalWeights]
    · exact le_rfl
    · exact mul_nonneg hr (ha _)
  have h := integral_abs_le_sqrt_sq (diagonalT_memLp hr ha)
  simp_rw [he, abs_of_nonneg (show 0 ≤ diagonalT r a _ from sqrt_nonneg _)] at h
  have hm : (∫ g, gaussianQuadratic (diagonalWeights r a) g
      ∂gaussianCoordinates (MatrixCoordinates ι)) = r * ∑ i, a i := by
    simpa only [gaussianCoordinates, diagonalWeights_sum] using gaussianQuadratic_mean (diagonalWeights r a)
  rwa [hm] at h

theorem goe_expected_top {j : ℝ} (hj : 0 ≤ j) :
    (∫ g, diagonalProcess (j/(Fintype.card ι:ℝ)) (fun _ : ι => 1) 1 0 g
      ∂gaussianCoordinates (MatrixCoordinates ι)) ≤ 2*sqrt j := by
  let r := j/(Fintype.card ι:ℝ)
  let a : ι → ℝ := fun _ => 1
  have hr : 0 ≤ r := div_nonneg hj (by positivity)
  have ha : ∀ i, 0 ≤ a i := by intro; norm_num [a]
  have hc := gaussian_quadraticSup_comparison (continuous_diagonalOffset a 1 0)
    ((continuous_diagonalSqrt a).comp continuous_subtype_val) hr 1
  change (∫ g, diagonalProcess r a 1 0 g ∂gaussianCoordinates (MatrixCoordinates ι)) ≤
    (∫ g, diagonalLinearProcess r a 1 0 g ∂gaussianCoordinates (MatrixCoordinates ι)) at hc
  have hb (g) : diagonalLinearProcess r a 1 0 g ≤ 2*diagonalT r a g := by
    have h := diagonalLinearProcess_le (A := 1) (b := 0) hr ha
      (by intro; exact le_rfl) zero_le_one (by norm_num : (0:ℝ) ≤ 1) le_rfl
      le_rfl (by norm_num) zero_le_one g
    simpa only [sub_zero, one_pow, sub_self, sqrt_zero, sqrt_one, mul_one,
      abs_of_nonneg (show 0 ≤ diagonalT r a g from sqrt_nonneg _), zero_add] using h
  have hi := diagonalT_integrable hr ha
  calc
    _ ≤ ∫ g, diagonalLinearProcess r a 1 0 g
        ∂gaussianCoordinates (MatrixCoordinates ι) := hc
    _ ≤ ∫ g, 2*diagonalT r a g ∂gaussianCoordinates (MatrixCoordinates ι) :=
      integral_mono (integrable_diagonalLinearProcess r a 1 0) (hi.const_mul 2) hb
    _ = 2 * ∫ g, diagonalT r a g ∂gaussianCoordinates (MatrixCoordinates ι) :=
      integral_const_mul _ _
    _ ≤ 2*sqrt (r * ∑ i, a i) := mul_le_mul_of_nonneg_left (diagonalT_mean_le hr ha) (by norm_num)
    _ = 2*sqrt j := by
      have hn : (Fintype.card ι:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      simp [a, r, hn]

lemma gaussianCoordinates_preserving_neg {κ : Type*} [Fintype κ] :
    MeasurePreserving (fun g : κ → ℝ => -g) (gaussianCoordinates κ)
      (gaussianCoordinates κ) := by
  apply measurePreserving_pi (f := fun _ => fun x : ℝ => -x)
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)
  intro i
  exact ⟨by fun_prop, by simpa using (gaussianReal_map_neg (μ := 0) (v := 1))⟩

theorem goe_top_tail {j ε : ℝ} (hj : 0 < j) (hε : 0 ≤ ε) :
    (gaussianCoordinates (MatrixCoordinates ι)).real
      {g | 2*sqrt j+ε < diagonalProcess (j/(Fintype.card ι:ℝ)) (fun _ : ι => 1) 1 0 g} ≤
      Real.exp (-ε^2*(Fintype.card ι:ℝ)/(π^2*j)) := by
  let r := j/(Fintype.card ι:ℝ)
  let P := diagonalProcess r (fun _ : ι => 1) 1 0
  have hn : 0 < (Fintype.card ι:ℝ) := by exact_mod_cast Fintype.card_pos
  have hr : 0 < r := div_pos hj hn
  have hL := diagonalProcess_lipschitz (a := fun _ : ι => 1) hr.le (fun _ => zero_le_one)
    (fun _ => le_rfl) zero_le_one (by norm_num : (0:ℝ) ≤ 1) 0
  have hLp : 0 < Real.toNNReal (1*sqrt (2*r)*1) := by
    rw [Real.toNNReal_pos]; positivity
  have ht := gaussianProduct_upper_tail_lipschitz hL hLp hε
  have hm := goe_expected_top (ι := ι) hj.le
  have hs : {g | 2*sqrt j+ε < P g} ⊆
      {g | ε ≤ P g - ∫ g, P g ∂gaussianCoordinates (MatrixCoordinates ι)} := by
    intro g hg
    change ε ≤ P g - ∫ g, P g ∂gaussianCoordinates (MatrixCoordinates ι)
    change _ < P g at hg
    change (∫ g, P g ∂gaussianCoordinates (MatrixCoordinates ι)) ≤ 2*sqrt j at hm
    linarith
  exact (measureReal_mono hs).trans (ht.trans_eq (by
    congr 1
    rw [Real.coe_toNNReal _ (by positivity)]
    simp only [one_mul, mul_one]
    rw [sq_sqrt (by positivity)]
    dsimp [r]
    field_simp))

end GOEProbability
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
end

end OAI
