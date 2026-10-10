import Mathlib
import OAI.Probability.SKGap.Localization.ResidualRecipe
import OAI.Probability.SKGap.Gaussian.AdaptiveInnovationSquareTails
import OAI.Probability.SKGap.Entropy.ProdFst

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
namespace SKGapCutoff.Regression

lemma ExponentialConvergence.upper_rare
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {S : ∀ n, H n → ℝ} {s B : ℝ} (hS : ExponentialConvergence ρ S s) (hB : s < B) :
    ExponentiallyRare ρ (fun n => {h | B ≤ S n h}) := by
  apply (hS (B-s) (sub_pos.mpr hB)).mono
  exact Filter.Eventually.of_forall (fun n h hh => by
    change B-s ≤ |S n h-s|
    exact (sub_le_sub_right hh s).trans (le_abs_self _))

lemma expConvergence_sum
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {ι : Type*} [Fintype ι] {S : ι → ∀ n, H n → ℝ} {s : ι → ℝ}
    (hS : ∀ i, ExponentialConvergence ρ (S i) (s i)) :
    ExponentialConvergence ρ (fun n h => ∑ i, S i n h) (∑ i, s i) := by
  have hh := ExponentialConvergence.pi_finite hS
  exact hh.continuous_map (by fun_prop : ContinuousAt (fun x : ι → ℝ => ∑ i, x i) s)

lemma linear_combination_weight_bound {E ι : Type*} [Fintype ι]
    (f : ι → E → ℝ) (a c : ι → ℝ) (x : E) :
    dist (∑ i, a i*f i x) (∑ i, c i*f i x) ≤ dist a c * ∑ i, |f i x| := by
  rw [Real.dist_eq, ← Finset.sum_sub_distrib, Finset.mul_sum]
  calc
    _ ≤ ∑ i, |a i*f i x-c i*f i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← sub_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (dist_le_pi_dist a c i) (abs_nonneg _)

lemma append_linear_combination_lipschitz {E : Type*} [PseudoMetricSpace E]
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (c : ι → ℝ) :
    LipschitzWith (max 1 (∑ i, ‖c i‖₊*K)) (fun x => (x,∑ i, c i*f i x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Prod.dist_eq]
  apply max_le
  · exact (by simp : dist x y ≤ (1:ℝ)*dist x y).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left (1:ℝ≥0) _) dist_nonneg)
  · exact (linear_combination_lipschitz f hf c).dist_le_mul x y |>.trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right (1:ℝ≥0) _) dist_nonneg)

theorem ExponentialEmpiricalConcentration.append_unbounded_linear
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E}
    {ν : Measure E} [IsProbabilityMeasure ν]
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i))
    (hT : ∀ j, ExponentialSquareTails ρ (fun n h i => f j (X n h i)))
    (hi : ∀ j, Integrable (fun x => f j x^2) ν)
    (C : ∀ n, H n → ι → ℝ) (c : ι → ℝ) (hC : ExponentialConvergence ρ C c) :
    ExponentialEmpiricalConcentration ρ (fun n h i => (X n h i,∑ j, C n h j*f j (X n h i)))
      (ν.map (fun x => (x,∑ j, c j*f j x))) ∧
    ExponentialSquareTails ρ (fun n h i => ∑ j, C n h j*f j (X n h i)) := by
  have hS := expConvergence_sum (fun j => hX.lipschitz_secondMoment (f j) (hf j) (hT j) (hi j))
  let s := ∑ j, ∫ x, f j x^2 ∂ν
  let D := (Fintype.card ι:ℝ)+|s|+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hrare : ExponentiallyRare ρ (fun n => {h | D ≤ (∑ i, ∑ j, |f j (X n h i)|)/(n:ℝ)}) := by
    apply (hS.upper_rare (B := |s|+1) (by change s < |s|+1; linarith [le_abs_self s])).mono
    filter_upwards [eventually_ge_atTop 1] with n hn
    intro h hh
    have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
    have hb : (∑ i, ∑ j, |f j (X n h i)|)/(n:ℝ) ≤
        (Fintype.card ι:ℝ)+∑ j, (∑ i, f j (X n h i)^2)/(n:ℝ) := by
      calc
        _ ≤ (∑ i : Fin n, ∑ j, (1+f j (X n h i)^2))/(n:ℝ) := by
          apply div_le_div_of_nonneg_right _ hnR.le
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          nlinarith [sq_nonneg (|f j (X n h i)|-1), sq_abs (f j (X n h i))]
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, mul_one, Fintype.card_fin]
          rw [Finset.sum_comm]
          simp only [← Finset.sum_div]
          field_simp
    change |s|+1 ≤ _
    dsimp [D] at hh
    linarith
  constructor
  · apply hX.parameter_map_weight C c hC (fun a x => (x,∑ j, a j*f j x))
      (append_linear_combination_lipschitz f hf c) (fun x => ∑ j, |f j x|) D hD
    · intro a x
      simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using
        linear_combination_weight_bound f a c x
    · exact hrare
  · apply ExponentialSquareTails.sum
    intro j
    exact (hT j).scalar_mul (hC.continuous_map (continuous_apply j).continuousAt)

theorem ExponentialEmpiricalConcentration.adaptive_affine_query
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) [∀ n, IsProbabilityMeasure (ρ n)]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (X : ∀ n, H n → Fin n → E) (hXm : ∀ n, Measurable (X n))
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (r : ℕ) (U : ∀ n, H n → Fin n → Fin r → ℝ) (q : ∀ n, H n → Fin n → ℝ)
    (hUm : ∀ n, Measurable (U n)) (hqm : ∀ n, Measurable (q n))
    (hU : ∀ n h a, ∑ i, U n h i a^2 ≤ 1) (hq : ∀ n h, ∑ i, q n h i^2 ≤ 1)
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) {K : ℝ≥0}
    (hf : ∀ j, LipschitzWith K (f j))
    (hT : ∀ j, ExponentialSquareTails ρ (fun n h i => f j (X n h i)))
    (hi : ∀ j, Integrable (fun x => f j x^2) ν)
    (C : ∀ n, H n → Option ι → ℝ) (c : Option ι → ℝ)
    (hC : ExponentialConvergence ρ C c) :
    let Y := fun n (z : H n × ((Fin n ⊕ Unit) → ℝ)) i => Real.sqrt n *
      queryInnovation (residualProjection (U n z.1)) (q n z.1) z.2 i
    ExponentialEmpiricalConcentration
      (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun n z i => ((X n z.1 i,Y n z i),
        C n z.1 none*Y n z i+∑ j, C n z.1 (some j)*f j (X n z.1 i)))
      ((ν.prod (gaussianReal 0 1)).map
        (fun z => (z,c none*z.2+∑ j, c (some j)*f j z.1))) ∧
    ExponentialSquareTails (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun n z i => C n z.1 none*Y n z i+∑ j, C n z.1 (some j)*f j (X n z.1 i)) := by
  let F : Option ι → E × ℝ → ℝ := fun j z => j.elim z.2 (fun a => f a z.1)
  have hF (j : Option ι) : LipschitzWith (max 1 K) (F j) := by
    cases j with
    | none => exact LipschitzWith.prod_snd.weaken (le_max_left _ _)
    | some j =>
      have h := (hf j).comp (LipschitzWith.prod_fst (α := E) (β := ℝ))
      simpa only [F, Option.elim_some, Function.comp_def] using h.weaken
        (by simpa only [mul_one] using le_max_right (1:ℝ≥0) K)
  have hFT (j : Option ι) : ExponentialSquareTails
      (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun n z i => F j (X n z.1 i,Real.sqrt n*
        queryInnovation (residualProjection (U n z.1)) (q n z.1) z.2 i)) := by
    cases j with
    | none => exact adaptive_innovation_squareTails ρ r U q hUm hqm hU hq
    | some j => exact (hT j).prod_fst (fun n => standardArrayLaw (Fin n ⊕ Unit))
  have hFi (j : Option ι) : Integrable (fun z => F j z^2) (ν.prod (gaussianReal 0 1)) := by
    cases j with
    | none => exact (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq.comp_snd ν
    | some j => exact (hi j).comp_fst (gaussianReal 0 1)
  have hh := (hX.adaptive_gaussian ρ ν X hXm r U q hUm hqm hU hq).append_unbounded_linear
    F hF hFT hFi (fun n z => C n z.1) c (hC.prod_fst (fun n => standardArrayLaw (Fin n ⊕ Unit)))
  simpa only [F, Fintype.sum_option, Option.elim_none, Option.elim_some] using hh

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology

end

end OAI
