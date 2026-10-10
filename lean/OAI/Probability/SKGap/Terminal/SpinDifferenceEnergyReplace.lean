import Mathlib
import OAI.Probability.SKGap.Matrix.NormalizedInfluence
import OAI.Probability.SKGap.Entropy.BoundGood
import OAI.Probability.SKGap.Terminal.SpinDifferenceEnergy
import OAI.Probability.SKGap.Localization.ComponentRefresh

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory ContinuousLinearMap
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open Filter Set Metric
open scoped Topology RealInnerProductSpace
open scoped BigOperators
open ContinuousLinearMap
open scoped BigOperators
open ContinuousLinearMap
open scoped Topology Interval
open MeasureTheory
open MeasureTheory
open scoped BigOperators Topology Interval
open MeasureTheory
open scoped BigOperators Topology Interval
open scoped Topology
open MeasureTheory
open scoped BigOperators Topology Interval
open scoped BigOperators Topology
namespace SKGapCutoff

lemma spinDifferenceEnergy_replace {n : ℕ} (x : Spin n) (j : Fin n) :
    spinDifferenceEnergy (replace x j false) (replace x j true) = 4 := by
  unfold spinDifferenceEnergy
  rw [Finset.sum_eq_single j]
  · norm_num [spin, replace]
  · intro i _ hij
    simp [spin, replace, Function.update_of_ne hij]
  · simp

lemma lipschitz_vector_derivativeSquare {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) {K : NNReal}
    (hF : LipschitzWith K F) (x : Spin n) :
    vectorDerivativeSquare (fun y i => F (spinEuclidean y) i) x ≤ (n:ℝ)*(K:ℝ)^2 := by
  have hh (j : Fin n) : (∑ i, (halfDiff j (fun y => F (spinEuclidean y) i) x)^2) ≤ (K:ℝ)^2 := by
    have hl := pow_le_pow_left₀ (norm_nonneg _)
      (hF.norm_sub_le (spinEuclidean (replace x j true)) (spinEuclidean (replace x j false))) 2
    rw [mul_pow, spinEuclidean_sub_norm_sq, spinDifferenceEnergy_replace,
      EuclideanSpace.real_norm_sq_eq] at hl
    have he : (∑ i, (halfDiff j (fun y => F (spinEuclidean y) i) x)^2) =
        (∑ i, (F (spinEuclidean (replace x j true)) i-F (spinEuclidean (replace x j false)) i)^2)/4 := by
      simp only [halfDiff, div_pow, ← Finset.sum_div]
      norm_num
    rw [he]
    change (∑ i, (F (spinEuclidean (replace x j true)) i-F (spinEuclidean (replace x j false)) i)^2) ≤ _ at hl
    linarith
  unfold vectorDerivativeSquare
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _j : Fin n, (K:ℝ)^2 := Finset.sum_le_sum (fun j _ => hh j)
    _ = _ := by simp

theorem refreshGradient_lipschitz_short_time {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) {K : NNReal}
    (hF : LipschitzWith K F) (m : VectorFields n) (hm : ∀ x i, |m x i|≤1)
    (C U M D t : ℝ) (hC : 0≤C) (hU : 0≤U) (hD : 0≤D) (ht : 0≤t)
    (hrough : ∀ q : VectorFields n, ∀ u : ℝ, 0≤u → ∀ x,
      vectorSquare (refreshGradientSemigroup m u q) x ≤
        Real.exp (C*u)*refreshSemigroup m u (vectorSquare q) x)
    (hbound : ∀ x, ‖F (spinEuclidean x)‖^2 ≤ U)
    (hrow : ∀ x i, ∑ j, refreshInfluence m x i j^2 ≤ D)
    (hop : ∀ x (q : Fin n → ℝ), ∑ i, (∑ j, refreshInfluence m x i j*q j)^2 ≤
      M^2*∑ i, q i^2) (x : Spin n) :
    vectorSquare (refreshGradientSemigroup m t (fun y i => F (spinEuclidean y) i)-
      (fun y i => F (spinEuclidean y) i)) x ≤
      2*t^2*Real.exp (2*C*t)*(3*(1+M^2)*U+12*D*(n:ℝ)*(K:ℝ)^2)+
        8*(n:ℝ)*(K:ℝ)^2*t := by
  have hb : ∀ x, vectorSquare (fun y i => F (spinEuclidean y) i) x ≤ U := by
    intro x
    simpa only [vectorSquare, ← EuclideanSpace.real_norm_sq_eq] using hbound x
  have hh := refreshGradient_short_time m (fun y i => F (spinEuclidean y) i) hm
    C U ((n:ℝ)*(K:ℝ)^2) M D t hC hU (by positivity) hD ht hrough hb
    (lipschitz_vector_derivativeSquare F hF) hrow hop x
  have ho := refresh_lipschitz_recipe_short_time F hF m hm t ht x
  simp only [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply] at ho
  nlinarith only [hh,ho]

lemma refreshInfluence_field_opNorm {n : ℕ} (H : VectorFields n) (C : ℝ) (hC : 0≤C)
    (hHC : ∀ x, ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (fun j i => halfDiff i (fun y => H y j) x)‖ ≤ C) (x : Spin n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (refreshInfluence (fun y k => Real.tanh (H y k)) x)‖ ≤ C+4*C^2 := by
  let K : Interaction n := fun j i => halfDiff i (fun y => H y j) x
  let A : Interaction n := refreshInfluence (fun y k => Real.tanh (H y k)) x
  let V : Interaction n := Matrix.diagonal (fun j => scalarVariance (H x j))
  let E := A-K.transpose*V
  have he (i j : Fin n) : |E i j| ≤ 4*(K j i)^2 := by
    simp only [E,A,K,V,Matrix.sub_apply,Matrix.mul_diagonal]
    exact refreshInfluence_error_le H x i j
  have hk : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) K‖ ≤ C := hHC x
  have hkt : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) K.transpose‖ ≤ C := by
    have hs : K.transpose = star K := rfl
    have hn : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) K.transpose‖ =
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) K‖ := by
      rw [hs,map_star]
      exact ContinuousLinearMap.adjoint.norm_map _
    rw [hn]
    exact hk
  have hv : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) V‖ ≤ 1 := by
    apply matrix_diagonal_opNorm_le _ 1 (by norm_num)
    intro j
    rw [abs_of_pos (scalarVariance_pos _)]
    exact scalarVariance_le_one _
  have herr : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) E‖ ≤ 4*C^2 := by
    apply matrix_opNorm_le_schur E _ (by positivity)
    · intro i
      calc
        _ ≤ ∑ j, 4*(K j i)^2 := Finset.sum_le_sum (fun j _ => he i j)
        _ = 4*∑ j, (K j i)^2 := (Finset.mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((RandomMatrix.matrix_column_sq_le K i).trans (pow_le_pow_left₀ (norm_nonneg _) hk 2)) (by norm_num)
    · intro j
      calc
        _ ≤ ∑ i, 4*(K j i)^2 := Finset.sum_le_sum (fun i _ => he i j)
        _ = 4*∑ i, (K j i)^2 := (Finset.mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((matrix_row_sq_le K j).trans (pow_le_pow_left₀ (norm_nonneg _) hk 2)) (by norm_num)
  have hbase : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (K.transpose*V)‖ ≤ C := by
    rw [map_mul]
    exact (norm_mul_le _ _).trans ((mul_le_mul hkt hv (norm_nonneg _) hC).trans_eq (mul_one C))
  have ha : A = K.transpose*V+E := by dsimp only [E]; abel
  change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ _
  rw [ha,map_add]
  exact (norm_add_le _ _).trans (add_le_add hbase herr)

lemma refreshVector_field_bound {n : ℕ} (H : VectorFields n) (C : ℝ) (hC : 0≤C)
    (hHC : ∀ x, ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (fun j i => halfDiff i (fun y => H y j) x)‖ ≤ C)
    (p : VectorFields n) (t : ℝ) (ht : 0≤t) (x : Spin n) :
    vectorSquare (refreshGradientSemigroup (fun y k => Real.tanh (H y k)) t p) x ≤
      Real.exp (preparationGrowth C*t)*refreshSemigroup (fun y k => Real.tanh (H y k)) t
        (vectorSquare p) x := by
  apply (refreshRough_of_field_opNorm H C hC hHC p t ht x).trans
  apply mul_le_mul_of_nonneg_right
  · apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ ht
    unfold preparationGrowth
    linarith
  · exact refreshSemigroup_nonneg _ (fun y k => (Real.abs_tanh_lt_one _).le) t ht _
      (fun y => Finset.sum_nonneg (fun i _ => sq_nonneg _)) x

theorem field_recipe_short_time {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) {K : NNReal}
    (hF : LipschitzWith K F) (H : VectorFields n) (C U t : ℝ)
    (hC : 0≤C) (hU : 0≤U) (ht : 0≤t)
    (hHC : ∀ x, ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (fun j i => halfDiff i (fun y => H y j) x)‖ ≤ C)
    (hbound : ∀ x, ‖F (spinEuclidean x)‖^2 ≤ U) (x : Spin n) :
    vectorSquare (refreshGradientSemigroup (fun y k => Real.tanh (H y k)) t
      (fun y i => F (spinEuclidean y) i)-(fun y i => F (spinEuclidean y) i)) x ≤
      2*t^2*Real.exp (2*preparationGrowth C*t)*
        (3*(1+(C+4*C^2)^2)*U+12*(C+4*C^2)^2*(n:ℝ)*(K:ℝ)^2)+
        8*(n:ℝ)*(K:ℝ)^2*t := by
  apply refreshGradient_lipschitz_short_time F hF _ (fun y k => (Real.abs_tanh_lt_one _).le)
    (preparationGrowth C) U (C+4*C^2) ((C+4*C^2)^2) t
    (preparationGrowth_pos C hC).le hU (sq_nonneg _) ht
    (refreshVector_field_bound H C hC hHC) hbound
  · intro y i
    exact (matrix_row_sq_le _ i).trans
      (pow_le_pow_left₀ (norm_nonneg _) (refreshInfluence_field_opNorm H C hC hHC y) 2)
  · intro y q
    exact Regression.matrix_mulVec_sq_bound _ q (refreshInfluence_field_opNorm H C hC hHC y)

end SKGapCutoff

open MeasureTheory
open scoped BigOperators Topology Interval RealInnerProductSpace

end

end OAI
