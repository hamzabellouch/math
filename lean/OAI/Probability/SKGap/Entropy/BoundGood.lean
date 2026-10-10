import Mathlib
import OAI.Probability.SKGap.Entropy.ParameterMapWeight
import OAI.Probability.SKGap.Gaussian.SquareTail2

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
namespace SKGapCutoff.Regression

lemma ExponentialConvergence.zero_of_bound_on_good
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {A B : ∀ n, H n → ℝ} (hB : ExponentialConvergence ρ B 0)
    {K : ℝ} (hK : 0 ≤ K) (G : ∀ n, Set (H n))
    (hrare : ExponentiallyRare ρ (fun n => (G n)ᶜ))
    (hAB : ∀ᶠ n in atTop, ∀ h ∈ G n, 0 ≤ A n h ∧ A n h ≤ K*B n h) :
    ExponentialConvergence ρ A 0 := by
  intro ε hε
  have hd : 0 < ε/(K+1) := div_pos hε (by linarith)
  apply (hrare.union (hB _ hd)).mono
  filter_upwards [hAB] with n hn
  intro h hh
  by_cases hg : h ∈ G n
  · apply Or.inr
    have hab := hn h hg
    simp only [Set.mem_ofPred_eq,Real.dist_eq,sub_zero,abs_of_nonneg hab.1] at hh
    change ε/(K+1) ≤ dist (B n h) 0
    rw [Real.dist_eq,sub_zero]
    have hb := le_abs_self (B n h)
    have hh' : ε ≤ K*|B n h| := hh.trans (hab.2.trans (mul_le_mul_of_nonneg_left hb hK))
    apply (div_le_iff₀ (by linarith : 0 < K+1)).mpr
    nlinarith [abs_nonneg (B n h)]
  · exact Or.inl hg

lemma matrix_mulVec_sq_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) {K : ℝ}
    (hA : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ K) :
    ∑ i, (A *ᵥ v) i^2 ≤ K^2*∑ i, v i^2 := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A
  let w : EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 _).symm v
  have hh : ‖T w‖ ≤ K*‖w‖ := (T.le_opNorm w).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
  rw [mul_pow,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq] at hs
  exact hs

theorem degenerate_matrix_query
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] (ρ : ∀ n, Measure (H n))
    (A : ∀ n, H n → Matrix (Fin n) (Fin n) ℝ) (v : ∀ n, H n → Fin n → ℝ)
    {K : ℝ} (_hK : 0 ≤ K)
    (hA : ExponentiallyRare ρ (fun n => {h | K < ‖Matrix.toEuclideanCLM
      (n := Fin n) (𝕜 := ℝ) (A n h)‖}))
    (hv : ExponentialConvergence ρ (fun n h => (∑ i, v n h i^2)/(n:ℝ)) 0) :
    ExponentialConvergence ρ (fun n h => (∑ i, ((A n h) *ᵥ v n h) i^2)/(n:ℝ)) 0 := by
  apply hv.zero_of_bound_on_good (K := K^2) (sq_nonneg K)
    (fun n => {h | ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (A n h)‖ ≤ K})
    (by simpa only [Set.compl_ofPred,not_le] using hA)
  apply Filter.Eventually.of_forall
  intro n h hh
  refine ⟨by positivity,?_⟩
  exact (div_le_div_of_nonneg_right (matrix_mulVec_sq_bound (A n h) (v n h) hh)
    (Nat.cast_nonneg _)).trans_eq (by ring)

theorem ExponentialEmpiricalConcentration.degenerate_append
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) {X : ∀ n, H n → Fin n → E}
    {p : ∀ n, H n → Fin n → ℝ} {ν : Measure (E × ℝ)}
    (hp : ExponentialEmpiricalConcentration ρ (fun n h i => (X n h i,p n h i)) ν)
    (hpT : ExponentialSquareTails ρ p)
    (A : ∀ n, H n → Matrix (Fin n) (Fin n) ℝ) (v : ∀ n, H n → Fin n → ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hA : ExponentiallyRare ρ (fun n => {h | K < ‖Matrix.toEuclideanCLM
      (n := Fin n) (𝕜 := ℝ) (A n h)‖}))
    (hv : ExponentialConvergence ρ (fun n h => (∑ i, v n h i^2)/(n:ℝ)) 0) :
    ExponentialEmpiricalConcentration ρ
      (fun n h i => (X n h i,p n h i+((A n h) *ᵥ v n h) i)) ν ∧
    ExponentialSquareTails ρ (fun n h i => p n h i+((A n h) *ᵥ v n h) i) := by
  have hm := degenerate_matrix_query ρ A v hK hA hv
  constructor
  · apply hp.l2_stability
    simpa only [Prod.dist_eq,dist_self,max_eq_right dist_nonneg,Real.dist_eq,
      sub_add_cancel_left,abs_neg,max_eq_right (abs_nonneg (_ : ℝ)),sq_abs] using hm
  · apply hpT.l2_stability
    simpa only [sub_add_cancel_left,neg_sq] using hm

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise

end

end OAI
