import Mathlib
import OAI.Probability.SKGap.Entropy.AdaptiveTrueAffineQuery
import OAI.Probability.SKGap.Matrix.CompletedMatrix
import OAI.Probability.SKGap.Entropy.OrthogonalCoefficients

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
namespace SKGapCutoff.Regression

local instance {n m : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin m → ℝ))

lemma integrable_residualRecipe_sq {E : Type*} [MeasurableSpace E]
    {ν : Measure E} {r : ℕ} (u : Fin r → E → ℝ) (g : E → ℝ) (c : Fin r → ℝ)
    (hu : ∀ a, AEStronglyMeasurable (u a) ν) (hg : AEStronglyMeasurable g ν)
    (hui : ∀ a, Integrable (fun x => u a x^2) ν) (hgi : Integrable (fun x => g x^2) ν) :
    Integrable (fun x => residualRecipe u g c x^2) ν := by
  have h := integrable_linear_combination_sq
    (fun a : Option (Fin r) => a.elim g u) (fun a : Option (Fin r) => a.elim 1 (fun a => -c a))
    (by intro a; cases a with | none => exact hg | some a => exact hu a)
    (by intro a; cases a with | none => exact hgi | some a => exact hui a)
  simpa only [Fintype.sum_option,Option.elim_none,Option.elim_some,one_mul,neg_mul,
    Finset.sum_neg_distrib,← sub_eq_add_neg,residualRecipe] using h

theorem ExponentialEmpiricalConcentration.nondegenerate_query_step
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) [∀ n, IsProbabilityMeasure (ρ n)]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (X : ∀ n, H n → Fin n → E) (hXm : ∀ n, Measurable (X n))
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (r : ℕ) (U Y : ∀ n, H n → Matrix (Fin n) (Fin r) ℝ)
    (hUm : ∀ n, Measurable (U n))
    (hU : ∀ n h a, ∑ i, U n h i a^2 ≤ 1)
    (G : ∀ n, Set (H n)) (hG : ∀ n, MeasurableSet (G n))
    (hrare : ExponentiallyRare ρ (fun n => (G n)ᶜ))
    (hgood : ∀ n h, h ∈ G n → (U n h)ᵀ*U n h=1)
    (u y : Fin r → E → ℝ) (g : E → ℝ) {K : ℝ≥0} (hK : 1 ≤ K)
    (hu : ∀ a, LipschitzWith K (u a)) (hy : ∀ a, LipschitzWith K (y a))
    (hg : LipschitzWith K g)
    (huT : ∀ a, ExponentialSquareTails ρ (fun n h i => u a (X n h i)))
    (hyT : ∀ a, ExponentialSquareTails ρ (fun n h i => y a (X n h i)))
    (hgT : ExponentialSquareTails ρ (fun n h i => g (X n h i)))
    (hui : ∀ a, Integrable (fun x => u a x^2) ν)
    (hyi : ∀ a, Integrable (fun x => y a x^2) ν) (hgi : Integrable (fun x => g x^2) ν)
    (heu : ∀ (n : ℕ) h i a, Real.sqrt n*U n h i a=u a (X n h i))
    (hey : ∀ (n : ℕ) h i a, Real.sqrt n*Y n h i a=y a (X n h i))
    (hs : 0 < ∫ x, residualRecipe u g (fun a => ∫ z, u a z*g z ∂ν) x^2 ∂ν) :
    let R := fun n h => residualProjection (U n h) *ᵥ (fun i => g (X n h i))
    let q := fun n h => unitVector (R n h)
    let s := ∫ x, residualRecipe u g (fun a => ∫ z, u a z*g z ∂ν) x^2 ∂ν
    let φ := fun x => (x,residualRecipe u g (fun a => ∫ z, u a z*g z ∂ν) x/Real.sqrt s)
    let ν' := ν.map φ
    let W := fun n (z : H n × ((Fin n × Fin n) → ℝ)) i =>
      Real.sqrt n*(completedMatrix (U n z.1) (Y n z.1) z.2 *ᵥ q n z.1) i
    ExponentialConvergence ρ (fun n h => (∑ i, R n h i^2)/(n:ℝ)) s ∧
    ExponentialEmpiricalConcentration
      (fun n => (ρ n).prod (standardArrayLaw (Fin n × Fin n)))
      (fun n z i => ((X n z.1 i,Real.sqrt n*q n z.1 i),W n z i))
      ((ν'.prod (gaussianReal 0 1)).map
        (fun z => (z.1,z.2+∑ a, (∫ x, y a x.1*x.2 ∂ν')*u a z.1.1))) ∧
    ExponentialSquareTails ρ (fun n h i => Real.sqrt n*q n h i) ∧
    ExponentialSquareTails (fun n => (ρ n).prod (standardArrayLaw (Fin n × Fin n))) W := by
  dsimp only
  let R := fun n h => residualProjection (U n h) *ᵥ (fun i => g (X n h i))
  let S := fun n h => (∑ i, R n h i^2)/(n:ℝ)
  let q := fun n h => unitVector (R n h)
  let c := fun a => ∫ z, u a z*g z ∂ν
  let s := ∫ x, residualRecipe u g c x^2 ∂ν
  let φ := fun x => (x,residualRecipe u g c x/Real.sqrt s)
  let ν' := ν.map φ
  have hφ : Measurable φ := by
    apply measurable_id.prodMk
    apply Measurable.div_const
    exact hg.continuous.measurable.sub (Finset.measurable_sum _ (fun a _ =>
      (hu a).continuous.measurable.const_mul (c a)))
  let : IsProbabilityMeasure ν' := inferInstance
  have hh := hX.normalized_projected_query U u g hu hg huT hgT hui hgi heu hs
  change ExponentialConvergence ρ S s ∧
    ExponentialEmpiricalConcentration ρ
      (fun n h i => (X n h i,Real.sqrt n*q n h i)) ν' ∧
    ExponentialSquareTails ρ (fun n h i => Real.sqrt n*q n h i) at hh
  let X' := fun n h i => (X n h i,Real.sqrt n*q n h i)
  have hRm n : Measurable (R n) := by
    have hP := measurable_residualProjection_comp (U n) (hUm n)
    have hgX : Measurable (fun h i => g (X n h i)) := by
      exact Measurable.of_eval (fun i => hg.continuous.measurable.comp
        ((measurable_pi_apply i).comp (hXm n)))
    apply Measurable.of_eval
    intro i
    simp only [R,Matrix.mulVec,dotProduct]
    apply Finset.measurable_sum
    intro j _
    exact (((measurable_pi_apply j).comp (measurable_pi_apply i)).comp hP).mul
      ((measurable_pi_apply j).comp hgX)
  have hqm n : Measurable (q n) := measurable_unitVector.comp (hRm n)
  have hSm n : Measurable (S n) := by
    apply Measurable.div_const
    exact Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_apply i).comp (hRm n)).pow_const 2))
  have hX'm n : Measurable (X' n) := by
    apply Measurable.of_eval
    intro i
    exact ((measurable_pi_apply i).comp (hXm n)).prodMk
      (((measurable_pi_apply i).comp (hqm n)).const_mul (Real.sqrt n))
  let G' := fun n => G n ∩ {h | 0 < S n h}
  have hG' n : MeasurableSet (G' n) := (hG n).inter
    (measurableSet_lt measurable_const (hSm n))
  have hrare' : ExponentiallyRare ρ (fun n => (G' n)ᶜ) := by
    apply (hrare.union (hh.1.positive_rare hs)).mono
    refine Filter.Eventually.of_forall ?_
    intro n h he
    by_cases hh : h ∈ G n
    · apply Or.inr
      change S n h ≤ 0
      exact le_of_not_gt (fun hp => he ⟨hh,hp⟩)
    · exact Or.inl hh
  have hgood' n h (he : h ∈ G' n) : (U n h)ᵀ*U n h=1 ∧
      (∑ i, q n h i^2)=1 ∧ (U n h)ᵀ *ᵥ q n h=0 := by
    have horth := hgood n h he.1
    refine ⟨horth,unitVector_sq_eq _ ?_,normalized_residual_perpendicular _ horth _⟩
    by_contra! hn
    have hnp : S n h ≤ 0 := div_nonpos_of_nonpos_of_nonneg hn (Nat.cast_nonneg n)
    exact not_le_of_gt he.2 hnp
  have hu' a : LipschitzWith K (fun z : E × ℝ => u a z.1) := by
    simpa only [Function.comp_def,mul_one] using (hu a).comp (LipschitzWith.prod_fst (α := E) (β := ℝ))
  have hy' a : LipschitzWith K (fun z : E × ℝ => y a z.1) := by
    simpa only [Function.comp_def,mul_one] using (hy a).comp (LipschitzWith.prod_fst (α := E) (β := ℝ))
  have hg' : LipschitzWith K (Prod.snd : E × ℝ → ℝ) :=
    LipschitzWith.prod_snd.weaken hK
  have hui' a : Integrable (fun z : E × ℝ => u a z.1^2) ν' := by
    apply (integrable_map_measure (((hu a).continuous.measurable.comp measurable_fst).pow_const 2).aestronglyMeasurable hφ.aemeasurable).2
    exact hui a
  have hyi' a : Integrable (fun z : E × ℝ => y a z.1^2) ν' := by
    apply (integrable_map_measure (((hy a).continuous.measurable.comp measurable_fst).pow_const 2).aestronglyMeasurable hφ.aemeasurable).2
    exact hyi a
  have hgi' : Integrable (fun z : E × ℝ => z.2^2) ν' := by
    rw [integrable_map_measure (by fun_prop) hφ.aemeasurable]
    simp only [φ,Function.comp_def,div_pow]
    exact (integrable_residualRecipe_sq u g c
      (fun a => (hu a).continuous.measurable.aestronglyMeasurable)
      hg.continuous.measurable.aestronglyMeasurable hui hgi).div_const _
  have hqle n h : ∑ i, q n h i^2 ≤ 1 := unitVector_sq_le _
  have hstep := hh.2.1.completed_normalized_query ρ ν' X' hX'm r U Y q
    hUm hqm hU hqle G' hG' hrare' hgood'
    (fun a z => u a z.1) (fun a z => y a z.1) Prod.snd hu' hy' hg'
    huT hyT hh.2.2 hui' hyi' hgi' heu hey (fun _ _ _ => rfl)
  exact ⟨hh.1,hstep.1,hh.2.2,hstep.2⟩

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator

end

end OAI
