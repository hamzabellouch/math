import Mathlib
import OAI.Probability.SKGap.Localization.IntegrableLinearCombinationSq
import OAI.Probability.SKGap.Localization.ProdEventSectionLaw

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
namespace SKGapCutoff.Regression

local instance queryEmpiricalMatrixMeasurable {n m : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin m → ℝ))

local instance queryEmpiricalMatrixBorel {n m : ℕ} : BorelSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin m → ℝ))

theorem ExponentialEmpiricalConcentration.adaptive_true_affine_query
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) [∀ n, IsProbabilityMeasure (ρ n)]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (X : ∀ n, H n → Fin n → E) (hXm : ∀ n, Measurable (X n))
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (r : ℕ) (U : ∀ n, H n → Matrix (Fin n) (Fin r) ℝ) (q : ∀ n, H n → Fin n → ℝ)
    (hUm : ∀ n, Measurable (U n)) (hqm : ∀ n, Measurable (q n))
    (hU : ∀ n h a, ∑ i, U n h i a^2 ≤ 1) (hq : ∀ n h, ∑ i, q n h i^2 ≤ 1)
    (G : ∀ n, Set (H n)) (hG : ∀ n, MeasurableSet (G n))
    (hrare : ExponentiallyRare ρ (fun n => (G n)ᶜ))
    (hgood : ∀ n h, h ∈ G n → (U n h)ᵀ*U n h=1 ∧
      (∑ i, q n h i^2)=1 ∧ (U n h)ᵀ *ᵥ q n h=0)
    {ι : Type*} [Fintype ι] (f : ι → E → ℝ) {K : ℝ≥0}
    (hf : ∀ j, LipschitzWith K (f j))
    (hT : ∀ j, ExponentialSquareTails ρ (fun n h i => f j (X n h i)))
    (hi : ∀ j, Integrable (fun x => f j x^2) ν)
    (C : ∀ n, H n → Option ι → ℝ) (c : Option ι → ℝ)
    (hCm : ∀ n, Measurable (C n)) (hC : ExponentialConvergence ρ C c) :
    let W := fun n (z : H n × ((Fin n × Fin n) → ℝ)) i =>
      C n z.1 none*(Real.sqrt n*queryAnswer (residualProjection (U n z.1)) (q n z.1) z.2 i)+
      ∑ j, C n z.1 (some j)*f j (X n z.1 i)
    ExponentialEmpiricalConcentration (fun n => (ρ n).prod (standardArrayLaw (Fin n × Fin n)))
      (fun n z i => (X n z.1 i,W n z i))
      ((ν.prod (gaussianReal 0 1)).map (fun z => (z.1,c none*z.2+∑ j, c (some j)*f j z.1))) ∧
    ExponentialSquareTails (fun n => (ρ n).prod (standardArrayLaw (Fin n × Fin n))) W := by
  let P := fun n h => residualProjection (U n h)
  let Ya := fun n (z : H n × ((Fin n × Fin n) → ℝ)) i =>
    C n z.1 none*(Real.sqrt n*queryAnswer (P n z.1) (q n z.1) z.2 i)+
      ∑ j, C n z.1 (some j)*f j (X n z.1 i)
  let Yb := fun n (z : H n × ((Fin n ⊕ Unit) → ℝ)) i =>
    C n z.1 none*(Real.sqrt n*queryInnovation (P n z.1) (q n z.1) z.2 i)+
      ∑ j, C n z.1 (some j)*f j (X n z.1 i)
  have hPm n : Measurable (P n) := measurable_residualProjection_comp (U n) (hUm n)
  have ha n : Measurable (Ya n) := by
    have hm := measurable_queryAnswer_comp (fun z : H n × ((Fin n × Fin n) → ℝ) => P n z.1)
      (fun z => q n z.1) Prod.snd (hPm n |>.comp measurable_fst)
      (hqm n |>.comp measurable_fst) measurable_snd
    apply Measurable.of_eval
    intro i
    dsimp [Ya]
    apply Measurable.add
    · exact ((measurable_pi_apply none).comp (hCm n |>.comp measurable_fst)).mul
        (measurable_const.mul ((measurable_pi_apply i).comp hm))
    · exact Finset.measurable_sum _ (fun j _ =>
        ((measurable_pi_apply (some j)).comp (hCm n |>.comp measurable_fst)).mul
          ((hf j).continuous.measurable.comp ((measurable_pi_apply i).comp (hXm n |>.comp measurable_fst))))
  have hb n : Measurable (Yb n) := by
    have hm := measurable_queryInnovation_comp (fun z : H n × ((Fin n ⊕ Unit) → ℝ) => P n z.1)
      (fun z => q n z.1) Prod.snd (hPm n |>.comp measurable_fst)
      (hqm n |>.comp measurable_fst) measurable_snd
    apply Measurable.of_eval
    intro i
    dsimp [Yb]
    apply Measurable.add
    · exact ((measurable_pi_apply none).comp (hCm n |>.comp measurable_fst)).mul
        (measurable_const.mul ((measurable_pi_apply i).comp hm))
    · exact Finset.measurable_sum _ (fun j _ =>
        ((measurable_pi_apply (some j)).comp (hCm n |>.comp measurable_fst)).mul
          ((hf j).continuous.measurable.comp ((measurable_pi_apply i).comp (hXm n |>.comp measurable_fst))))
  have hlaw : ∀ᶠ n in atTop, ∀ h ∈ G n,
      (standardArrayLaw (Fin n × Fin n)).map (fun a => Ya n (h,a)) =
        (standardArrayLaw (Fin n ⊕ Unit)).map (fun b => Yb n (h,b)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    intro h hh
    obtain ⟨hu,hunit,ho⟩ := hgood n h hh
    have hpq : P n h*queryColumn (q n h)=queryColumn (q n h) := by
      have he : P n h *ᵥ q n h=q n h := by
        simp only [P,residualProjection,Matrix.sub_mulVec,Matrix.one_mulVec,
          ← Matrix.mulVec_mulVec,ho,Matrix.mulVec_zero,sub_zero]
      ext i j
      simpa only [Matrix.mul_apply,queryColumn,Matrix.mulVec,dotProduct] using congrFun he i
    have he := query_innovation_law hn (P n h) (residualProjection_symmetric (U n h))
      (residualProjection_idem (U n h) hu) (q n h) hunit hpq
    let ψ : (Fin n → ℝ) → Fin n → ℝ := fun a i =>
      C n h none*(Real.sqrt n*a i)+∑ j, C n h (some j)*f j (X n h i)
    have hmψ : Measurable ψ := by dsimp [ψ]; fun_prop
    change (standardArrayLaw (Fin n × Fin n)).map (queryAnswer (P n h) (q n h)) =
      (standardArrayLaw (Fin n ⊕ Unit)).map (queryInnovation (P n h) (q n h)) at he
    have hh := congrArg (Measure.map ψ) he
    rw [Measure.map_map hmψ (queryAnswer_measurable (P n h) (q n h)),
      Measure.map_map hmψ (queryInnovation_measurable (P n h) (q n h))] at hh
    exact hh
  have hproxy := hX.adaptive_affine_query ρ ν X hXm r U q hUm hqm hU hq f hf hT hi C c hC
  let φ : (E × ℝ) × ℝ → E × ℝ := fun z => (z.1.1,z.2)
  have hφ : LipschitzWith 1 φ := by
    simpa using (LipschitzWith.prod_fst.comp (LipschitzWith.prod_fst (α := E × ℝ) (β := ℝ))).prodMk
      LipschitzWith.prod_snd
  have hproxyE := hproxy.1.map φ hφ
  have hmζ : Measurable (fun z : E × ℝ => (z,c none*z.2+∑ j, c (some j)*f j z.1)) := by
    apply measurable_id.prodMk
    exact (measurable_const.mul measurable_snd).add
      (Finset.measurable_sum _ (fun j _ => measurable_const.mul ((hf j).continuous.measurable.comp measurable_fst)))
  rw [Measure.map_map hφ.continuous.measurable hmζ] at hproxyE
  constructor
  · apply ExponentialEmpiricalConcentration.of_section_law ρ
      (fun n => standardArrayLaw (Fin n × Fin n)) (fun n => standardArrayLaw (Fin n ⊕ Unit))
      (fun n z i => (X n z.1 i,Ya n z i)) (fun n z i => (X n z.1 i,Yb n z i))
      (fun n => Measurable.of_eval (fun i =>
        ((measurable_pi_apply i).comp (hXm n |>.comp measurable_fst)).prodMk ((measurable_pi_apply i).comp (ha n))))
      (fun n => Measurable.of_eval (fun i =>
        ((measurable_pi_apply i).comp (hXm n |>.comp measurable_fst)).prodMk ((measurable_pi_apply i).comp (hb n))))
      G hG hrare ?_ hproxyE
    filter_upwards [hlaw] with n hn
    intro h hh
    let ψ : (Fin n → ℝ) → Fin n → E × ℝ := fun a i => (X n h i,a i)
    have hmψ : Measurable ψ := by dsimp [ψ]; fun_prop
    have he := congrArg (Measure.map ψ) (hn h hh)
    rw [Measure.map_map hmψ (show Measurable (fun a => Ya n (h,a)) from (ha n).comp measurable_prodMk_left),
      Measure.map_map hmψ (show Measurable (fun b => Yb n (h,b)) from (hb n).comp measurable_prodMk_left)] at he
    exact he
  · exact ExponentialSquareTails.of_section_law ρ
      (fun n => standardArrayLaw (Fin n × Fin n)) (fun n => standardArrayLaw (Fin n ⊕ Unit))
      Ya Yb ha hb G hG hrare hlaw hproxy.2

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise

namespace SKGapCutoff.Regression

local instance completedQueryMatrixMeasurable {n m : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin m → ℝ))

lemma ExponentialConvergence.constant
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)] (ρ : ∀ n, Measure (H n))
    {E : Type*} [PseudoMetricSpace E] (x : E) :
    ExponentialConvergence ρ (fun _ _ => x) x := by
  intro ε hε
  refine ⟨1,1,by norm_num,by norm_num,Filter.Eventually.of_forall ?_⟩
  intro n
  simp [dist_self,not_le.mpr hε]

lemma ExponentialEmpiricalConcentration.congr_on_good
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X Y : ∀ n, H n → Fin n → E} {ν : Measure E}
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (G : ∀ n, Set (H n)) (hrare : ExponentiallyRare ρ (fun n => (G n)ᶜ))
    (he : ∀ᶠ n in atTop, ∀ h ∈ G n, Y n h = X n h) :
    ExponentialEmpiricalConcentration ρ Y ν := by
  intro f K hf B hB ε hε
  have hr : ExponentiallyRare ρ (fun n => {h | ε ≤ |(∑ i, f (X n h i))/(n:ℝ)-∫ x, f x ∂ν|}) :=
    hX f K hf B hB ε hε
  apply (hr.union hrare).mono
  filter_upwards [he] with n hn
  intro h hh
  by_cases hg : h ∈ G n
  · exact Or.inl (by simpa only [Set.mem_ofPred_eq,hn h hg] using hh)
  · exact Or.inr hg

lemma ExponentialSquareTails.congr_on_good
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {X Y : ∀ n, H n → Fin n → ℝ}
    (hX : ExponentialSquareTails ρ X)
    (G : ∀ n, Set (H n)) (hrare : ExponentiallyRare ρ (fun n => (G n)ᶜ))
    (he : ∀ᶠ n in atTop, ∀ h ∈ G n, Y n h = X n h) :
    ExponentialSquareTails ρ Y := by
  intro ε hε
  obtain ⟨R,hR,ht⟩ := hX ε hε
  refine ⟨R,hR,?_⟩
  apply (ht.union hrare).mono
  filter_upwards [he] with n hn
  intro h hh
  by_cases hg : h ∈ G n
  · exact Or.inl (by simpa only [Set.mem_ofPred_eq,hn h hg] using hh)
  · exact Or.inr hg

theorem ExponentialEmpiricalConcentration.completed_normalized_query
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) [∀ n, IsProbabilityMeasure (ρ n)]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (X : ∀ n, H n → Fin n → E) (hXm : ∀ n, Measurable (X n))
    (hX : ExponentialEmpiricalConcentration ρ X ν)
    (r : ℕ) (U Y : ∀ n, H n → Matrix (Fin n) (Fin r) ℝ) (q : ∀ n, H n → Fin n → ℝ)
    (hUm : ∀ n, Measurable (U n)) (hqm : ∀ n, Measurable (q n))
    (hU : ∀ n h a, ∑ i, U n h i a^2 ≤ 1) (hq : ∀ n h, ∑ i, q n h i^2 ≤ 1)
    (G : ∀ n, Set (H n)) (hG : ∀ n, MeasurableSet (G n))
    (hrare : ExponentiallyRare ρ (fun n => (G n)ᶜ))
    (hgood : ∀ n h, h ∈ G n → (U n h)ᵀ*U n h=1 ∧
      (∑ i, q n h i^2)=1 ∧ (U n h)ᵀ *ᵥ q n h=0)
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
    let W := fun n (z : H n × ((Fin n × Fin n) → ℝ)) i => Real.sqrt n*
      ((revealedCompletion (U n z.1) (Y n z.1)+
        residualProjection (U n z.1)*goe z.2*residualProjection (U n z.1)) *ᵥ q n z.1) i
    let law := (ν.prod (gaussianReal 0 1)).map
      (fun z => (z.1,z.2+∑ a, (∫ x, y a x*g x ∂ν)*u a z.1))
    ExponentialEmpiricalConcentration (fun n => (ρ n).prod (standardArrayLaw (Fin n × Fin n)))
      (fun n z i => (X n z.1 i,W n z i)) law ∧
    ExponentialSquareTails (fun n => (ρ n).prod (standardArrayLaw (Fin n × Fin n))) W := by
  let C : ∀ n, H n → Option (Fin r) → ℝ := fun n h a => a.elim 1
    (fun a => (∑ i, y a (X n h i)*g (X n h i))/(n:ℝ))
  let c : Option (Fin r) → ℝ := fun a => a.elim 1 (fun a => ∫ x, y a x*g x ∂ν)
  have hCm n : Measurable (C n) := by
    apply Measurable.of_eval
    intro a
    cases a with
    | none => exact measurable_const
    | some a =>
      apply Measurable.div_const
      exact Finset.measurable_sum _ (fun i _ =>
        ((hy a).continuous.measurable.comp ((measurable_pi_apply i).comp (hXm n))).mul
          (hg.continuous.measurable.comp ((measurable_pi_apply i).comp (hXm n))))
  have hC : ExponentialConvergence ρ C c := by
    apply ExponentialConvergence.pi_finite
    intro a
    cases a with
    | none => exact ExponentialConvergence.constant ρ 1
    | some a => exact hX.product_average (y a) g (hy a) hg (hyT a) hgT (hyi a) hgi
  have hp := hX.adaptive_true_affine_query ρ ν X hXm r U q hUm hqm hU hq
    G hG hrare hgood u hu huT hui C c hCm hC
  let Wb := fun n (z : H n × ((Fin n × Fin n) → ℝ)) i =>
    Real.sqrt n*queryAnswer (residualProjection (U n z.1)) (q n z.1) z.2 i+
      ∑ a, ((∑ j, y a (X n z.1 j)*g (X n z.1 j))/(n:ℝ))*u a (X n z.1 i)
  simp only [C,c,Option.elim_none,Option.elim_some,one_mul] at hp
  let Wa := fun n (z : H n × ((Fin n × Fin n) → ℝ)) i => Real.sqrt n*
      ((revealedCompletion (U n z.1) (Y n z.1)+
        residualProjection (U n z.1)*goe z.2*residualProjection (U n z.1)) *ᵥ q n z.1) i
  have he : ∀ᶠ n in atTop, ∀ z : H n × ((Fin n × Fin n) → ℝ), z.1 ∈ G n → Wa n z=Wb n z := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    intro z hz
    have ho := (hgood n z.1 hz).2.2
    have hPq : residualProjection (U n z.1) *ᵥ q n z.1=q n z.1 := by
      rw [residualProjection,Matrix.sub_mulVec,Matrix.one_mulVec,← Matrix.mulVec_mulVec,
        ho,Matrix.mulVec_zero,sub_zero]
    funext i
    dsimp [Wa,Wb]
    rw [completed_query_answer _ _ _ _ ho hPq]
    simp only [Pi.add_apply,mul_add,scaled_query_predictor hn,heu,hey,heq]
    simp only [mul_comm,add_comm]
  have hr := hrare.prod_fst (fun n => standardArrayLaw (Fin n × Fin n))
  constructor
  · apply hp.1.congr_on_good (fun n => Prod.fst ⁻¹' G n) hr
    filter_upwards [he] with n hn
    intro z hz
    funext i
    exact congrArg (fun t => (X n z.1 i,t i)) (hn z hz)
  · exact hp.2.congr_on_good (fun n => Prod.fst ⁻¹' G n) hr he

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise

end

end OAI
