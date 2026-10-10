import Mathlib
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
namespace SKGapCutoff.Regression

lemma ExponentiallyRare.prod_fst
    {H A : ℕ → Type*} [∀ n, MeasurableSpace (H n)] [∀ n, MeasurableSpace (A n)]
    {ρ : ∀ n, Measure (H n)} (μ : ∀ n, Measure (A n))
    [∀ n, IsProbabilityMeasure (μ n)] {S : ∀ n, Set (H n)}
    (hS : ExponentiallyRare ρ S) :
    ExponentiallyRare (fun n => (ρ n).prod (μ n)) (fun n => Prod.fst ⁻¹' S n) := by
  obtain ⟨C,c,hC,hc,he⟩ := hS
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [he] with n hn
  have hs : Prod.fst ⁻¹' S n = S n ×ˢ (Set.univ : Set (A n)) := by ext; simp
  rw [hs]
  exact (Measure.prod_prod_le _ _).trans (by simpa using hn)

lemma ExponentialSquareTails.prod_fst
    {H A : ℕ → Type*} [∀ n, MeasurableSpace (H n)] [∀ n, MeasurableSpace (A n)]
    {ρ : ∀ n, Measure (H n)} (μ : ∀ n, Measure (A n))
    [∀ n, IsProbabilityMeasure (μ n)] {X : ∀ n, H n → Fin n → ℝ}
    (hX : ExponentialSquareTails ρ X) :
    ExponentialSquareTails (fun n => (ρ n).prod (μ n)) (fun n z => X n z.1) := by
  intro ε hε
  obtain ⟨R,hR,ht⟩ := hX ε hε
  exact ⟨R,hR,ht.prod_fst μ⟩

lemma ExponentialConvergence.prod_fst
    {H A : ℕ → Type*} [∀ n, MeasurableSpace (H n)] [∀ n, MeasurableSpace (A n)]
    {ρ : ∀ n, Measure (H n)} (μ : ∀ n, Measure (A n))
    [∀ n, IsProbabilityMeasure (μ n)] {E : Type*} [PseudoMetricSpace E]
    {X : ∀ n, H n → E} {x : E} (hX : ExponentialConvergence ρ X x) :
    ExponentialConvergence (fun n => (ρ n).prod (μ n)) (fun n z => X n z.1) x := by
  intro ε hε
  exact (hX ε hε).prod_fst μ

lemma exponentialSquareTails_of_bounded
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) (X : ∀ n, H n → Fin n → ℝ) (B : ℝ)
    (hB : ∀ n h i, |X n h i| ≤ B) : ExponentialSquareTails ρ X := by
  intro ε hε
  refine ⟨|B|+1,by positivity, (exponentiallyRare_empty ρ).mono ?_⟩
  filter_upwards [] with n
  intro h hh
  have hz : ∀ i, squareTail (|B|+1) (X n h i) = 0 := by
    intro i
    have hb := (hB n h i).trans (le_abs_self B)
    simp [squareTail, show ¬ |B|+1 < |X n h i| by linarith]
  simp only [Set.mem_ofPred_eq, hz, Finset.sum_const_zero, zero_div] at hh
  exact False.elim ((not_le_of_gt hε) hh)

lemma ExponentialSquareTails.scalar_mul
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → ℝ}
    (hX : ExponentialSquareTails ρ X) {C : ∀ n, H n → ℝ} {c : ℝ}
    (hC : ExponentialConvergence ρ C c) :
    ExponentialSquareTails ρ (fun n h i => C n h*X n h i) := by
  intro ε hε
  let B := |c|+1
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨R,hR,ht⟩ := hX (ε/B^2) (by positivity)
  refine ⟨B*R,by positivity, (ht.union (hC 1 (by norm_num))).mono ?_⟩
  filter_upwards [] with n
  intro h hh
  by_cases hc : 1 ≤ dist (C n h) c
  · exact Or.inr hc
  apply Or.inl
  have hcb : |C n h| ≤ B := by
    rw [Real.dist_eq] at hc
    have := abs_add_le (C n h-c) c
    rw [sub_add_cancel] at this
    dsimp [B]
    linarith [lt_of_not_ge hc]
  have hb : (∑ i, squareTail (B*R) (C n h*X n h i))/(n:ℝ) ≤
      B^2*((∑ i, squareTail R (X n h i))/(n:ℝ)) := by
    calc
      _ ≤ (∑ i, B^2*squareTail R (X n h i))/(n:ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum (fun i _ => squareTail_mul R _ _ _ hR.le hcb)
      _ = _ := by rw [← Finset.mul_sum]; ring
  change ε/B^2 ≤ (∑ i, squareTail R (X n h i))/(n:ℝ)
  apply (div_le_iff₀ (sq_pos_of_pos hB)).mpr
  exact (show ε ≤ _ from hh).trans (by simpa [mul_comm] using hb)

lemma ExponentialSquareTails.sum
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] {ρ : ∀ n, Measure (H n)}
    {ι : Type*} [Fintype ι] (X : ι → ∀ n, H n → Fin n → ℝ)
    (hX : ∀ j, ExponentialSquareTails ρ (X j)) :
    ExponentialSquareTails ρ (fun n h i => ∑ j, X j n h i) := by
  classical
  have hh (s : Finset ι) : ExponentialSquareTails ρ (fun n h i => ∑ j ∈ s, X j n h i) := by
    induction s using Finset.induction_on with
    | empty =>
        simpa using exponentialSquareTails_of_bounded ρ (fun _ _ _ => (0:ℝ)) 0
          (by intros; simp)
    | @insert j s hj ih =>
        simpa only [Finset.sum_insert hj] using (hX j).add ih
  exact hh Finset.univ

lemma integrable_mul_of_sq {E : Type*} [MeasurableSpace E] {ν : Measure E}
    {f g : E → ℝ} (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν)
    (hi : Integrable (fun x => f x^2) ν) (hj : Integrable (fun x => g x^2) ν) :
    Integrable (fun x => f x*g x) ν := by
  apply (hi.add hj).mono' (hf.mul hg)
  filter_upwards [] with x
  change |f x*g x| ≤ f x^2+g x^2
  rw [abs_mul]
  nlinarith [sq_nonneg (|f x|-|g x|), sq_abs (f x), sq_abs (g x)]

lemma integrable_add_sq {E : Type*} [MeasurableSpace E] {ν : Measure E}
    {f g : E → ℝ} (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν)
    (hi : Integrable (fun x => f x^2) ν) (hj : Integrable (fun x => g x^2) ν) :
    Integrable (fun x => (f x+g x)^2) ν := by
  apply ((hi.add hj).const_mul 2).mono' ((hf.add hg).pow 2)
  filter_upwards [] with x
  change |(f x+g x)^2| ≤ 2*(f x^2+g x^2)
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (f x-g x)]

lemma ExponentialEmpiricalConcentration.lipschitz_secondMoment
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E}
    {ν : Measure E} [IsProbabilityMeasure ν]
    (hX : ExponentialEmpiricalConcentration ρ X ν) (f : E → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f)
    (hT : ExponentialSquareTails ρ (fun n h i => f (X n h i)))
    (hi : Integrable (fun x => f x^2) ν) :
    ExponentialConvergence ρ (fun n h => (∑ i, f (X n h i)^2)/(n:ℝ))
      (∫ x, f x^2 ∂ν) := by
  have : IsProbabilityMeasure (ν.map f) := inferInstance
  have him : Integrable (fun x : ℝ => x^2) (ν.map f) := by
    rw [integrable_map_measure (by fun_prop) hf.continuous.measurable.aemeasurable]
    exact hi
  have hh := (hX.map f hf).secondMoment hT him
  rw [integral_map hf.continuous.measurable.aemeasurable (by fun_prop)] at hh
  exact hh

lemma ExponentialEmpiricalConcentration.product_average
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E}
    {ν : Measure E} [IsProbabilityMeasure ν]
    (hX : ExponentialEmpiricalConcentration ρ X ν) (f g : E → ℝ) {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hT : ExponentialSquareTails ρ (fun n h i => f (X n h i)))
    (hS : ExponentialSquareTails ρ (fun n h i => g (X n h i)))
    (hi : Integrable (fun x => f x^2) ν) (hj : Integrable (fun x => g x^2) ν) :
    ExponentialConvergence ρ (fun n h => (∑ i, f (X n h i)*g (X n h i))/(n:ℝ))
      (∫ x, f x*g x ∂ν) := by
  have hm := hf.continuous.measurable.aestronglyMeasurable (μ := ν)
  have hn := hg.continuous.measurable.aestronglyMeasurable (μ := ν)
  have hij := integrable_mul_of_sq hm hn hi hj
  have hs := hX.lipschitz_secondMoment (fun x => f x+g x) (hf.add hg) (hT.add hS)
    (integrable_add_sq hm hn hi hj)
  have hh := (hs.prod ((hX.lipschitz_secondMoment f hf hT hi).prod
    (hX.lipschitz_secondMoment g hg hS hj))).continuous_map
      (f := fun z : ℝ × ℝ × ℝ => (z.1-z.2.1-z.2.2)/2) (by fun_prop)
  have hid (n : ℕ) (h : H n) :
      ((∑ i, (f (X n h i)+g (X n h i))^2)/(n:ℝ) -
        (∑ i, f (X n h i)^2)/(n:ℝ) -
        (∑ i, g (X n h i)^2)/(n:ℝ))/2 =
        (∑ i, f (X n h i)*g (X n h i))/(n:ℝ) := by
    rw [← sub_div, ← sub_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    have he i : (f (X n h i)+g (X n h i))^2-f (X n h i)^2-g (X n h i)^2 =
        2*(f (X n h i)*g (X n h i)) := by ring
    simp_rw [he]
    rw [← Finset.mul_sum]
    ring
  have hie : ((∫ x, (f x+g x)^2 ∂ν)-(∫ x, f x^2 ∂ν)-(∫ x, g x^2 ∂ν))/2 =
      ∫ x, f x*g x ∂ν := by
    have he x : (f x+g x)^2 = f x^2+g x^2+2*(f x*g x) := by ring
    simp_rw [he]
    rw [integral_add (show Integrable (fun x => f x^2+g x^2) ν from hi.add hj)
      (hij.const_mul 2), integral_add hi hj, integral_const_mul]
    ring
  simpa only [hid, hie] using hh

lemma ExponentialEmpiricalConcentration.unbounded_gram
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X : ∀ n, H n → Fin n → E}
    {ν : Measure E} [IsProbabilityMeasure ν]
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) {K : ℝ≥0}
    (hf : ∀ j, LipschitzWith K (f j))
    (hT : ∀ j, ExponentialSquareTails ρ (fun n h i => f j (X n h i)))
    (hi : ∀ j, Integrable (fun x => f j x^2) ν) :
    ExponentialConvergence ρ
      (fun n h j k => (∑ i, f j (X n h i)*f k (X n h i))/(n:ℝ))
      (fun j k => ∫ x, f j x*f k x ∂ν) := by
  apply ExponentialConvergence.pi_finite
  intro j
  apply ExponentialConvergence.pi_finite
  intro k
  exact hX.product_average (f j) (f k) (hf j) (hf k) (hT j) (hT k) (hi j) (hi k)

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology

end

end OAI
