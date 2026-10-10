import Mathlib
import OAI.Probability.SKGap.Localization.IntegrableResidualRecipeSq
import OAI.Probability.SKGap.Localization.RegeneratedAnswer

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
namespace SKGapCutoff.Regression

local instance iteratedMatrixMeasurable {n m : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin m → ℝ))

theorem ExponentialEmpiricalConcentration.regenerated_normalized_query
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) [∀ n, IsProbabilityMeasure (ρ n)]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (X : ∀ n, H n → Fin n → E) (hXm : ∀ n, Measurable (X n))
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (r : ℕ) (U Y : ∀ n, H n → Matrix (Fin n) (Fin r) ℝ) (q : ∀ n, H n → Fin n → ℝ)
    (hUm : ∀ n, Measurable (U n)) (hqm : ∀ n, Measurable (q n))
    (hU : ∀ n h a, ∑ i, U n h i a^2 ≤ 1) (hq : ∀ n h, ∑ i, q n h i^2 ≤ 1)
    (u y : Fin r → E → ℝ) (g : E → ℝ) {K : ℝ≥0}
    (hu : ∀ a, LipschitzWith K (u a)) (hy : ∀ a, LipschitzWith K (y a)) (hg : LipschitzWith K g)
    (huT : ∀ a, ExponentialSquareTails ρ (fun n h i => u a (X n h i)))
    (hyT : ∀ a, ExponentialSquareTails ρ (fun n h i => y a (X n h i)))
    (hgT : ExponentialSquareTails ρ (fun n h i => g (X n h i)))
    (hui : ∀ a, Integrable (fun x => u a x^2) ν)
    (hyi : ∀ a, Integrable (fun x => y a x^2) ν) (hgi : Integrable (fun x => g x^2) ν)
    (heu : ∀ (n : ℕ) h i a, Real.sqrt n*U n h i a=u a (X n h i))
    (hey : ∀ (n : ℕ) h i a, Real.sqrt n*Y n h i a=y a (X n h i))
    (heq : ∀ (n : ℕ) h i, Real.sqrt n*q n h i=g (X n h i)) :
    let W := fun n (z : H n × ((Fin n ⊕ Unit) → ℝ)) i =>
      Real.sqrt n*regeneratedAnswer (U n z.1) (Y n z.1) (q n z.1) z.2 i
    let law := (ν.prod (gaussianReal 0 1)).map
      (fun z => (z.1,z.2+∑ a, (∫ x, y a x*g x ∂ν)*u a z.1))
    ExponentialEmpiricalConcentration (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun n z i => (X n z.1 i,W n z i)) law ∧
    ExponentialSquareTails (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit))) W := by
  let C : ∀ n, H n → Option (Fin r) → ℝ := fun n h a => a.elim 1
    (fun a => (∑ i, y a (X n h i)*g (X n h i))/(n:ℝ))
  let c : Option (Fin r) → ℝ := fun a => a.elim 1 (fun a => ∫ x, y a x*g x ∂ν)
  have hC : ExponentialConvergence ρ C c := by
    apply ExponentialConvergence.pi_finite
    intro a
    cases a with
    | none => exact ExponentialConvergence.constant ρ 1
    | some a => exact hX.product_average (y a) g (hy a) hg (hyT a) hgT (hyi a) hgi
  have hp := hX.adaptive_affine_query ρ ν X hXm r U q hUm hqm hU hq
    u hu huT hui C c hC
  simp only [C,c,Option.elim_none,Option.elim_some,one_mul] at hp
  let φ : (E × ℝ) × ℝ → E × ℝ := fun z => (z.1.1,z.2)
  have hφ : LipschitzWith 1 φ := by
    simpa using (LipschitzWith.prod_fst.comp
      (LipschitzWith.prod_fst (α := E × ℝ) (β := ℝ))).prodMk LipschitzWith.prod_snd
  have hpE := hp.1.map φ hφ
  have hm : Measurable (fun z : E × ℝ =>
      (z,z.2+∑ a, (∫ x, y a x*g x ∂ν)*u a z.1)) := by
    apply measurable_id.prodMk
    exact measurable_snd.add (Finset.measurable_sum _ (fun a _ =>
      measurable_const.mul ((hu a).continuous.measurable.comp measurable_fst)))
  rw [Measure.map_map hφ.continuous.measurable hm] at hpE
  have he (n : ℕ) (z : H n × ((Fin n ⊕ Unit) → ℝ)) (i : Fin n) :
      Real.sqrt n*regeneratedAnswer (U n z.1) (Y n z.1) (q n z.1) z.2 i =
        Real.sqrt n*queryInnovation (residualProjection (U n z.1)) (q n z.1) z.2 i+
          ∑ a, ((∑ j, y a (X n z.1 j)*g (X n z.1 j))/(n:ℝ))*u a (X n z.1 i) := by
    have hn : 0<n := Nat.pos_of_ne_zero (fun hn => by subst n; exact Fin.elim0 i)
    simp only [regeneratedAnswer,Pi.add_apply,mul_add,scaled_query_predictor hn,heu,hey,heq]
    simp only [mul_comm,add_comm]
  dsimp only
  simp only [he]
  exact ⟨hpE,hp.2⟩

theorem ExponentialEmpiricalConcentration.regenerated_nondegenerate_step
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
    let W := fun n (z : H n × ((Fin n ⊕ Unit) → ℝ)) i =>
      Real.sqrt n*(regeneratedAnswer (U n z.1) (Y n z.1) (q n z.1) z.2) i
    ExponentialConvergence ρ (fun n h => (∑ i, R n h i^2)/(n:ℝ)) s ∧
    ExponentialEmpiricalConcentration
      (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun n z i => ((X n z.1 i,Real.sqrt n*q n z.1 i),W n z i))
      ((ν'.prod (gaussianReal 0 1)).map
        (fun z => (z.1,z.2+∑ a, (∫ x, y a x.1*x.2 ∂ν')*u a z.1.1))) ∧
    ExponentialSquareTails ρ (fun n h i => Real.sqrt n*q n h i) ∧
    ExponentialSquareTails (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit))) W := by
  dsimp only
  let R := fun n h => residualProjection (U n h) *ᵥ (fun i => g (X n h i))
  let q := fun n h => unitVector (R n h)
  let S := fun n h => (∑ i, R n h i^2)/(n:ℝ)
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
  have hX'm n : Measurable (X' n) := by
    apply Measurable.of_eval
    intro i
    exact ((measurable_pi_apply i).comp (hXm n)).prodMk
      (((measurable_pi_apply i).comp (hqm n)).const_mul (Real.sqrt n))
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
  have hstep := hh.2.1.regenerated_normalized_query ρ ν' X' hX'm r U Y q
    hUm hqm hU hqle
    (fun a z => u a z.1) (fun a z => y a z.1) Prod.snd hu' hy' hg'
    huT hyT hh.2.2 hui' hyi' hgi' heu hey (fun _ _ _ => rfl)
  exact ⟨hh.1,hstep.1,hh.2.2,hstep.2⟩

@[fun_prop] lemma measurable_extendFrame_comp {n r : ℕ} {H : Type*} [MeasurableSpace H]
    (U : H → Matrix (Fin n) (Fin r) ℝ) (q : H → Fin n → ℝ)
    (hU : Measurable U) (hq : Measurable q) : Measurable (fun h => extendFrame (U h) (q h)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro a
  obtain rfl | ⟨a,rfl⟩ := Fin.eq_zero_or_eq_succ a
  · exact (measurable_pi_apply i).comp hq
  · exact ((measurable_pi_apply a).comp (measurable_pi_apply i)).comp hU

lemma extended_normalized_columns_bound {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (v : Fin n → ℝ) (hU : ∀ a, ∑ i, U i a^2 ≤ 1) (a : Fin (r+1)) :
    ∑ i, extendFrame U (unitVector v) i a^2 ≤ 1 := by
  obtain rfl | ⟨a,rfl⟩ := Fin.eq_zero_or_eq_succ a
  · exact unitVector_sq_le v
  · exact hU a

theorem regenerated_good_history
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) [∀ n, IsProbabilityMeasure (ρ n)]
    (r : ℕ) (U Y : ∀ n, H n → Matrix (Fin n) (Fin r) ℝ)
    (v : ∀ n, H n → Fin n → ℝ)
    (G : ∀ n, Set (H n)) (hrare : ExponentiallyRare ρ (fun n => (G n)ᶜ))
    (hgood : ∀ n h, h ∈ G n → (U n h)ᵀ*U n h=1 ∧ (U n h)ᵀ*Y n h=(Y n h)ᵀ*U n h)
    (s : ℝ) (hs : 0 < s)
    (hS : ExponentialConvergence ρ
      (fun n h => (∑ i, (residualProjection (U n h) *ᵥ v n h) i^2)/(n:ℝ)) s) :
    let q := fun n h => unitVector (residualProjection (U n h) *ᵥ v n h)
    let G' := fun n => G n ∩ {h | 0 < (∑ i, (residualProjection (U n h) *ᵥ v n h) i^2)/(n:ℝ)}
    ExponentiallyRare (fun n => (ρ n).prod (standardArrayLaw (Fin n ⊕ Unit)))
      (fun n => {z | z.1 ∉ G' n}) ∧
    (∀ n (z : H n × ((Fin n ⊕ Unit) → ℝ)), z.1 ∈ G' n →
      let U' := extendFrame (U n z.1) (q n z.1)
      let Y' := extendFrame (Y n z.1) (regeneratedAnswer (U n z.1) (Y n z.1) (q n z.1) z.2)
      U'ᵀ*U'=1 ∧ U'ᵀ*Y'=Y'ᵀ*U') := by
  dsimp only
  let S := fun n h => (∑ i, (residualProjection (U n h) *ᵥ v n h) i^2)/(n:ℝ)
  have hr : ExponentiallyRare ρ (fun n => (G n ∩ {h | 0 < S n h})ᶜ) := by
    apply (hrare.union (hS.positive_rare hs)).mono
    refine Filter.Eventually.of_forall ?_
    intro n h he
    by_cases hh : h ∈ G n
    · apply Or.inr
      change S n h ≤ 0
      exact le_of_not_gt (fun hp => he ⟨hh,hp⟩)
    · exact Or.inl hh
  refine ⟨hr.prod_fst (fun n => standardArrayLaw (Fin n ⊕ Unit)), ?_⟩
  intro n z hz
  obtain ⟨hU,hY⟩ := hgood n z.1 hz.1
  have ho := normalized_residual_perpendicular (U n z.1) hU (v n z.1)
  have hq : ∑ i, (unitVector (residualProjection (U n z.1) *ᵥ v n z.1)) i^2=1 := by
    apply unitVector_sq_eq
    by_contra! hn
    have hnp := div_nonpos_of_nonpos_of_nonneg hn (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    exact not_le_of_gt hz.2 hnp
  exact ⟨extendFrame_orthonormal _ _ hU hq ho,
    regenerated_frame_compatible _ _ _ hU hY ho z.2⟩

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise

end

end OAI
