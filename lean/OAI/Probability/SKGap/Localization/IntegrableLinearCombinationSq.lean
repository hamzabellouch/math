import Mathlib
import OAI.Probability.SKGap.Entropy.UpperRare

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
namespace SKGapCutoff.Regression

lemma integrable_linear_combination_sq
    {E ι : Type*} [MeasurableSpace E] [Fintype ι] {ν : Measure E}
    (f : ι → E → ℝ) (c : ι → ℝ)
    (hm : ∀ i, AEStronglyMeasurable (f i) ν)
    (hi : ∀ i, Integrable (fun x => f i x^2) ν) :
    Integrable (fun x => (∑ i, c i*f i x)^2) ν := by
  have hpoint x : (∑ i, c i*f i x)^2 = ∑ i, ∑ j, c i*(f i x*f j x)*c j := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hpoint]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact ((integrable_mul_of_sq (hm i) (hm j) (hi i) (hi j)).const_mul (c i)).mul_const (c j)

theorem ExponentialEmpiricalConcentration.unbounded_linear_energy
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E}
    {ν : Measure E} [IsProbabilityMeasure ν]
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i))
    (hT : ∀ j, ExponentialSquareTails ρ (fun n h i => f j (X n h i)))
    (hi : ∀ j, Integrable (fun x => f j x^2) ν)
    (C : ∀ n, H n → ι → ℝ) (c : ι → ℝ) (hC : ExponentialConvergence ρ C c) :
    ExponentialConvergence ρ (fun n h => (∑ i, (∑ j, C n h j*f j (X n h i))^2)/(n:ℝ))
      (∫ x, (∑ j, c j*f j x)^2 ∂ν) := by
  have hh := hX.append_unbounded_linear f hf hT hi C c hC
  let φ : E → E × ℝ := fun x => (x,∑ j, c j*f j x)
  have hφ : Measurable φ := (append_linear_combination_lipschitz f hf c).continuous.measurable
  have hiφ : Integrable (fun z : E × ℝ => z.2^2) (ν.map φ) := by
    rw [integrable_map_measure (by fun_prop) hφ.aemeasurable]
    exact integrable_linear_combination_sq f c (fun i => (hf i).continuous.measurable.aestronglyMeasurable) hi
  have hs := hh.1.lipschitz_secondMoment Prod.snd LipschitzWith.prod_snd hh.2 hiφ
  rw [integral_map hφ.aemeasurable (by fun_prop)] at hs
  exact hs

theorem ExponentialEmpiricalConcentration.normalized_unbounded_linear
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E}
    {ν : Measure E} [IsProbabilityMeasure ν]
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i))
    (hT : ∀ j, ExponentialSquareTails ρ (fun n h i => f j (X n h i)))
    (hi : ∀ j, Integrable (fun x => f j x^2) ν)
    (C : ∀ n, H n → ι → ℝ) (c : ι → ℝ) (hC : ExponentialConvergence ρ C c)
    (hs : 0 < ∫ x, (∑ j, c j*f j x)^2 ∂ν) :
    let S := fun n h => (∑ i, (∑ j, C n h j*f j (X n h i))^2)/(n:ℝ)
    let s := ∫ x, (∑ j, c j*f j x)^2 ∂ν
    ExponentialConvergence ρ S s ∧
    ExponentialEmpiricalConcentration ρ
      (fun n h i => (X n h i,(∑ j, C n h j*f j (X n h i))/Real.sqrt (S n h)))
      (ν.map (fun x => (x,(∑ j, c j*f j x)/Real.sqrt s))) ∧
    ExponentialSquareTails ρ
      (fun n h i => (∑ j, C n h j*f j (X n h i))/Real.sqrt (S n h)) := by
  let S := fun n h => (∑ i, (∑ j, C n h j*f j (X n h i))^2)/(n:ℝ)
  let s := ∫ x, (∑ j, c j*f j x)^2 ∂ν
  have hS : ExponentialConvergence ρ S s := hX.unbounded_linear_energy f hf hT hi C c hC
  have hc : ContinuousAt (fun z : (ι → ℝ) × ℝ => fun j => z.1 j/Real.sqrt z.2) (c,s) := by
    apply continuousAt_pi.mpr
    intro j
    exact ((continuous_apply j).comp continuous_fst).continuousAt.div
      (Real.continuous_sqrt.comp continuous_snd).continuousAt (ne_of_gt (Real.sqrt_pos.mpr hs))
  have hcoeff := (hC.prod hS).continuous_map hc
  have hh := hX.append_unbounded_linear f hf hT hi _ _ hcoeff
  simp only [div_mul_eq_mul_div, ← Finset.sum_div] at hh
  exact ⟨hS,hh⟩

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology

namespace SKGapCutoff.Regression

lemma revealedCompletion_mulVec {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (v : Fin n → ℝ) :
    revealedCompletion U Y *ᵥ v = Y *ᵥ (Uᵀ *ᵥ v)+U *ᵥ (Yᵀ *ᵥ v) -
      U *ᵥ ((Uᵀ*Y) *ᵥ (Uᵀ *ᵥ v)) := by
  simp only [revealedCompletion, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma revealedCompletion_perpendicular {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (q : Fin n → ℝ) (hq : Uᵀ *ᵥ q = 0) :
    revealedCompletion U Y *ᵥ q = U *ᵥ (Yᵀ *ᵥ q) := by
  simp only [revealedCompletion_mulVec, hq, Matrix.mulVec_zero, zero_add, sub_zero]

lemma queryAnswer_mulVec {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (g : (Fin n × Fin n) → ℝ) :
    queryAnswer P q g = P *ᵥ (goe g *ᵥ q) := by
  rw [Matrix.mulVec_mulVec]
  ext i
  simp only [queryAnswer, Matrix.mul_apply, queryColumn,
    Matrix.mulVec, dotProduct]

lemma completed_query_answer {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (q : Fin n → ℝ) (g : (Fin n × Fin n) → ℝ) (hq : Uᵀ *ᵥ q = 0)
    (hPq : residualProjection U *ᵥ q = q) :
    (revealedCompletion U Y+residualProjection U*goe g*residualProjection U) *ᵥ q =
      U *ᵥ (Yᵀ *ᵥ q)+queryAnswer (residualProjection U) q g := by
  rw [Matrix.add_mulVec, revealedCompletion_perpendicular U Y q hq]
  simp only [← Matrix.mulVec_mulVec, hPq, queryAnswer_mulVec]

lemma scaled_query_predictor {n r : ℕ} (hn : 0 < n)
    (U Y : Matrix (Fin n) (Fin r) ℝ) (q : Fin n → ℝ) (i : Fin n) :
    Real.sqrt n*(U *ᵥ (Yᵀ *ᵥ q)) i =
      ∑ a, (Real.sqrt n*U i a)*((∑ j, (Real.sqrt n*Y j a)*(Real.sqrt n*q j))/(n:ℝ)) := by
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hs : (Real.sqrt (n:ℝ))^2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  field_simp
  nlinarith [congrArg (fun z : ℝ => z*(U i a*Y j a*q j)) hs]

def extendFrame {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (q : Fin n → ℝ) :
    Matrix (Fin n) (Fin (r+1)) ℝ := fun i => Fin.cons (q i) (U i)

lemma extendFrame_zero {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (q : Fin n → ℝ)
    (i : Fin n) : extendFrame U q i 0 = q i := rfl

lemma extendFrame_succ {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (q : Fin n → ℝ)
    (i : Fin n) (a : Fin r) : extendFrame U q i a.succ = U i a := rfl

lemma extendFrame_orthonormal {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (q : Fin n → ℝ) (hU : Uᵀ*U=1) (hq : ∑ i, q i^2=1) (ho : Uᵀ *ᵥ q=0) :
    (extendFrame U q)ᵀ*extendFrame U q=1 := by
  ext a b
  obtain ha | ⟨a, rfl⟩ := Fin.eq_zero_or_eq_succ a
  · subst a
    obtain hb | ⟨b,rfl⟩ := Fin.eq_zero_or_eq_succ b
    · subst b
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, extendFrame_zero,
        Matrix.one_apply_eq, ← pow_two] using hq
    · have hb := congrFun ho b
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, extendFrame_zero,
        extendFrame_succ, Matrix.one_apply, Ne.symm (Fin.succ_ne_zero b), ↓reduceIte,
        Matrix.mulVec, dotProduct, Pi.zero_apply, mul_comm] using hb
  · obtain hb | ⟨b,rfl⟩ := Fin.eq_zero_or_eq_succ b
    · subst b
      have ha := congrFun ho a
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, extendFrame_zero,
        extendFrame_succ, Matrix.one_apply, Fin.succ_ne_zero, ↓reduceIte,
        Matrix.mulVec, dotProduct, Pi.zero_apply] using ha
    · have hab := congrFun (congrFun hU a) b
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, extendFrame_succ,
        Matrix.one_apply, Fin.succ_inj] using hab

lemma extendFrame_projection {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (q : Fin n → ℝ) :
    residualProjection (extendFrame U q) = queryComplement (residualProjection U) q := by
  ext i j
  simp only [residualProjection, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_succ, extendFrame_zero, extendFrame_succ,
    queryComplement_apply]
  ring

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology

end

end OAI
