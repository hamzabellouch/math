import Mathlib
import OAI.Probability.SKGap.Localization.IntegrableResidualRecipeSq

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
namespace SKGapCutoff.Regression

local instance rawQueryMatrixMeasurable {n m : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin m → ℝ))

lemma sqrt_sum_smul_unitVector {n : ℕ} (v : Fin n → ℝ) :
    Real.sqrt (∑ j, v j^2) • unitVector v = v := by
  have hs : 0 ≤ ∑ j, v j^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hz : ∑ j, v j^2=0
  · have hv : ∀ i, v i=0 := by
      intro i
      have hh : v i^2 ≤ ∑ j, v j^2 := Finset.single_le_sum
        (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
      rw [hz] at hh
      nlinarith [sq_nonneg (v i)]
    ext i
    simp only [Pi.smul_apply,smul_eq_mul,unitVector,hv,mul_zero,zero_div]
  · ext i
    change Real.sqrt (∑ j, v j^2)*(v i/Real.sqrt (∑ j, v j^2))=v i
    exact mul_div_cancel₀ _ (ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne hs (Ne.symm hz))))

lemma completedMatrix_scaled_input {n r : ℕ} (hn : 0 < n)
    (U Y : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ*U=1) (hY : Uᵀ*Y=Yᵀ*U)
    (v : Fin n → ℝ) (z : (Fin n × Fin n) → ℝ) (i : Fin n) :
    (completedMatrix U Y z *ᵥ v) i =
      Real.sqrt ((∑ j, (residualProjection U *ᵥ v) j^2)/(n:ℝ))*
        (Real.sqrt n*(completedMatrix U Y z *ᵥ unitVector (residualProjection U *ᵥ v)) i)+
      ∑ a, ((∑ j, Real.sqrt n*U j a*v j)/(n:ℝ))*(Real.sqrt n*Y i a) := by
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hsn : Real.sqrt (n:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hs : (Real.sqrt (n:ℝ))^2=n := Real.sq_sqrt (Nat.cast_nonneg _)
  rw [completedMatrix_input_decomposition U Y hU hY v z]
  simp only [Pi.add_apply]
  have hp : (Y *ᵥ (Uᵀ *ᵥ v)) i =
      ∑ a, ((∑ j, Real.sqrt n*U j a*v j)/(n:ℝ))*(Real.sqrt n*Y i a) := by
    simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_div,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
    nlinarith [congrArg (fun t : ℝ => t*(U j a*v j*Y i a)) hs]
  rw [hp,add_comm]
  congr 1
  conv_lhs => rw [← sqrt_sum_smul_unitVector (residualProjection U *ᵥ v)]
  rw [Matrix.mulVec_smul]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [Real.sqrt_div (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  field_simp

theorem ExponentialEmpiricalConcentration.unnormalized_query_assembly
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) [∀ n, IsProbabilityMeasure (ρ n)]
    (X : ∀ n, H n → Fin n → E)
    {r : ℕ} (U Y : ∀ n, H n → Matrix (Fin n) (Fin r) ℝ)
    (u y : Fin r → E → ℝ) (g : E → ℝ) {K : ℝ≥0} (hK : 1 ≤ K)
    (hy : ∀ a, LipschitzWith K (y a))
    (hyT : ∀ a, ExponentialSquareTails ρ (fun n h i => y a (X n h i)))
    (heu : ∀ (n : ℕ) h i a, Real.sqrt n*U n h i a=u a (X n h i))
    (hey : ∀ (n : ℕ) h i a, Real.sqrt n*Y n h i a=y a (X n h i))
    (G : ∀ n, Set (H n)) (hrare : ExponentiallyRare ρ (fun n => (G n)ᶜ))
    (hgood : ∀ n h, h ∈ G n → (U n h)ᵀ*U n h=1 ∧ (U n h)ᵀ*Y n h=(Y n h)ᵀ*U n h)
    (c : Fin r → ℝ) (s : ℝ)
    (hC : ExponentialConvergence ρ
      (fun n h a => (∑ i, u a (X n h i)*g (X n h i))/(n:ℝ)) c)
    (hS : ExponentialConvergence ρ
      (fun n h => (∑ i, (residualProjection (U n h) *ᵥ (fun j => g (X n h j))) i^2)/(n:ℝ)) s)
    (ν : Measure ((E × ℝ) × ℝ)) [IsProbabilityMeasure ν]
    (hX : ExponentialEmpiricalConcentration
      (fun n => (ρ n).prod (standardArrayLaw (Fin n × Fin n)))
      (fun n z i => ((X n z.1 i, Real.sqrt n*
        unitVector (residualProjection (U n z.1) *ᵥ (fun j => g (X n z.1 j))) i),
        Real.sqrt n*(completedMatrix (U n z.1) (Y n z.1) z.2 *ᵥ
          unitVector (residualProjection (U n z.1) *ᵥ (fun j => g (X n z.1 j)))) i)) ν)
    (hWT : ExponentialSquareTails
      (fun n => (ρ n).prod (standardArrayLaw (Fin n × Fin n)))
      (fun n z i => Real.sqrt n*(completedMatrix (U n z.1) (Y n z.1) z.2 *ᵥ
        unitVector (residualProjection (U n z.1) *ᵥ (fun j => g (X n z.1 j)))) i))
    (hyi : ∀ a, Integrable (fun z => y a z.1.1^2) ν)
    (hWi : Integrable (fun z => z.2^2) ν) :
    ExponentialEmpiricalConcentration
      (fun n => (ρ n).prod (standardArrayLaw (Fin n × Fin n)))
      (fun n z i => (((X n z.1 i, Real.sqrt n*
        unitVector (residualProjection (U n z.1) *ᵥ (fun j => g (X n z.1 j))) i),
        Real.sqrt n*(completedMatrix (U n z.1) (Y n z.1) z.2 *ᵥ
          unitVector (residualProjection (U n z.1) *ᵥ (fun j => g (X n z.1 j)))) i),
          (completedMatrix (U n z.1) (Y n z.1) z.2 *ᵥ (fun j => g (X n z.1 j))) i))
      (ν.map (fun z => (z,Real.sqrt s*z.2+∑ a, c a*y a z.1.1))) ∧
    ExponentialSquareTails (fun n => (ρ n).prod (standardArrayLaw (Fin n × Fin n)))
      (fun n z i => (completedMatrix (U n z.1) (Y n z.1) z.2 *ᵥ (fun j => g (X n z.1 j))) i) := by
  let f : Option (Fin r) → ((E × ℝ) × ℝ) → ℝ := fun a =>
    a.elim Prod.snd (fun a z => y a z.1.1)
  let C : ∀ n, H n → Option (Fin r) → ℝ := fun n h a => a.elim
    (Real.sqrt ((∑ i, (residualProjection (U n h) *ᵥ (fun j => g (X n h j))) i^2)/(n:ℝ)))
    (fun a => (∑ i, u a (X n h i)*g (X n h i))/(n:ℝ))
  let c' : Option (Fin r) → ℝ := fun a => a.elim (Real.sqrt s) c
  have hcoef : ExponentialConvergence ρ C c' := by
    apply ExponentialConvergence.pi_finite
    intro a
    cases a with
    | none => exact hS.continuous_map Real.continuous_sqrt.continuousAt
    | some a => exact hC.continuous_map (continuous_apply a).continuousAt
  have hf : ∀ a, LipschitzWith K (f a) := by
    intro a
    cases a with
    | none => exact LipschitzWith.prod_snd.weaken hK
    | some a =>
      simpa only [f,Option.elim_some,Function.comp_def,mul_one] using
        ((hy a).comp LipschitzWith.prod_fst).comp LipschitzWith.prod_fst
  have ht := hX.append_unbounded_linear f hf
    (fun a => by
      cases a with
      | none => exact hWT
      | some a => exact (hyT a).prod_fst (fun n => standardArrayLaw (Fin n × Fin n)))
    (fun a => by cases a with | none => exact hWi | some a => exact hyi a)
    (fun n z => C n z.1) c' (hcoef.prod_fst (fun n => standardArrayLaw (Fin n × Fin n)))
  simp only [f,C,c',Fintype.sum_option,Option.elim_none,Option.elim_some] at ht
  have he : ∀ᶠ n in atTop, ∀ z : H n × ((Fin n × Fin n) → ℝ), z.1 ∈ G n →
      ∀ i : Fin n,
      Real.sqrt ((∑ j, (residualProjection (U n z.1) *ᵥ (fun k => g (X n z.1 k))) j^2)/(n:ℝ))*
        (Real.sqrt n*(completedMatrix (U n z.1) (Y n z.1) z.2 *ᵥ
          unitVector (residualProjection (U n z.1) *ᵥ (fun k => g (X n z.1 k)))) i)+
      ∑ a, ((∑ j, u a (X n z.1 j)*g (X n z.1 j))/(n:ℝ))*y a (X n z.1 i) =
      (completedMatrix (U n z.1) (Y n z.1) z.2 *ᵥ (fun j => g (X n z.1 j))) i := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    intro z hz i
    have h := completedMatrix_scaled_input hn (U n z.1) (Y n z.1)
      (hgood n z.1 hz).1 (hgood n z.1 hz).2 (fun j => g (X n z.1 j)) z.2 i
    simpa only [heu,hey] using h.symm
  have hr := hrare.prod_fst (fun n => standardArrayLaw (Fin n × Fin n))
  constructor
  · apply ht.1.congr_on_good (fun n => Prod.fst ⁻¹' G n) hr
    filter_upwards [he] with n hn
    intro z hz
    funext i
    congr 1
    exact (hn z hz i).symm
  · apply ht.2.congr_on_good (fun n => Prod.fst ⁻¹' G n) hr
    filter_upwards [he] with n hn
    intro z hz
    funext i
    exact (hn z hz i).symm

noncomputable def normalizedRecipeLaw {E : Type*} [MeasurableSpace E]
    {r : ℕ} (ν : Measure E) (u y : Fin r → E → ℝ) (g : E → ℝ) :
    Measure ((E × ℝ) × ℝ) :=
  let c := fun a => ∫ x, u a x*g x ∂ν
  let s := ∫ x, residualRecipe u g c x^2 ∂ν
  let μ := ν.map (fun x => (x,residualRecipe u g c x/Real.sqrt s))
  (μ.prod (gaussianReal 0 1)).map
    (fun z => (z.1,z.2+∑ a, (∫ x, y a x.1*x.2 ∂μ)*u a z.1.1))

lemma normalizedRecipeLaw_probability {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {r : ℕ} (ν : Measure E) [IsProbabilityMeasure ν]
    (u y : Fin r → E → ℝ) (g : E → ℝ)
    (hu : ∀ a, Measurable (u a)) (hg : Measurable g) :
    IsProbabilityMeasure (normalizedRecipeLaw ν u y g) := by
  unfold normalizedRecipeLaw
  have hm : Measurable (fun x => (x,residualRecipe u g (fun a => ∫ x, u a x*g x ∂ν) x /
      Real.sqrt (∫ x, residualRecipe u g (fun a => ∫ x, u a x*g x ∂ν) x^2 ∂ν))) := by
    unfold residualRecipe
    exact measurable_id.prodMk ((hg.sub (Finset.measurable_sum _
      (fun a _ => (hu a).const_mul _))).div_const _)
  let := (Measure.isProbabilityMeasure_map_iff (μ := ν) hm.aemeasurable).2 inferInstance
  refine (Measure.isProbabilityMeasure_map_iff ?_).2 inferInstance
  apply Measurable.aemeasurable
  refine measurable_fst.prodMk (measurable_snd.add ?_)
  exact Finset.measurable_sum _ (fun a _ =>
    ((hu a).comp (measurable_fst.comp measurable_fst)).const_mul _)

lemma normalizedRecipeLaw_moments {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {r : ℕ} (ν : Measure E) [IsProbabilityMeasure ν]
    (u y : Fin r → E → ℝ) (g : E → ℝ)
    (hu : ∀ a, Measurable (u a)) (hy : ∀ a, Measurable (y a)) (hg : Measurable g)
    (hui : ∀ a, Integrable (fun x => u a x^2) ν)
    (hyi : ∀ a, Integrable (fun x => y a x^2) ν)
    (hgi : Integrable (fun x => g x^2) ν) :
    (∀ a, Integrable (fun z => u a z.1.1^2) (normalizedRecipeLaw ν u y g)) ∧
    (∀ a, Integrable (fun z => y a z.1.1^2) (normalizedRecipeLaw ν u y g)) ∧
    Integrable (fun z => z.1.2^2) (normalizedRecipeLaw ν u y g) ∧
    Integrable (fun z => z.2^2) (normalizedRecipeLaw ν u y g) := by
  let c := fun a => ∫ x, u a x*g x ∂ν
  let s := ∫ x, residualRecipe u g c x^2 ∂ν
  let φ := fun x => (x,residualRecipe u g c x/Real.sqrt s)
  let μ := ν.map φ
  let b := fun a => ∫ x, y a x.1*x.2 ∂μ
  let T := fun z : (E × ℝ) × ℝ => (z.1,z.2+∑ a, b a*u a z.1.1)
  have hφ : Measurable φ := by
    exact measurable_id.prodMk ((hg.sub (Finset.measurable_sum _
      (fun a _ => (hu a).const_mul _))).div_const _)
  let : IsProbabilityMeasure μ := inferInstance
  have hTm : Measurable T := measurable_fst.prodMk (measurable_snd.add
    (Finset.measurable_sum _ (fun a _ =>
      ((hu a).comp (measurable_fst.comp measurable_fst)).const_mul _)))
  have hu' a : Integrable (fun x : E × ℝ => u a x.1^2) μ := by
    apply (integrable_map_measure (((hu a).comp measurable_fst).pow_const 2).aestronglyMeasurable hφ.aemeasurable).2
    exact hui a
  have hy' a : Integrable (fun x : E × ℝ => y a x.1^2) μ := by
    apply (integrable_map_measure (((hy a).comp measurable_fst).pow_const 2).aestronglyMeasurable hφ.aemeasurable).2
    exact hyi a
  have hq : Integrable (fun x : E × ℝ => x.2^2) μ := by
    rw [integrable_map_measure (by fun_prop) hφ.aemeasurable]
    simp only [φ,Function.comp_def,div_pow]
    exact (integrable_residualRecipe_sq u g c (fun a => (hu a).aestronglyMeasurable)
      hg.aestronglyMeasurable hui hgi).div_const _
  change (∀ a, Integrable (fun z => u a z.1.1^2) ((μ.prod (gaussianReal 0 1)).map T)) ∧
    (∀ a, Integrable (fun z => y a z.1.1^2) ((μ.prod (gaussianReal 0 1)).map T)) ∧
    Integrable (fun z => z.1.2^2) ((μ.prod (gaussianReal 0 1)).map T) ∧
    Integrable (fun z => z.2^2) ((μ.prod (gaussianReal 0 1)).map T)
  refine ⟨?_,?_,?_,?_⟩
  · intro a
    apply (integrable_map_measure (((hu a).comp (measurable_fst.comp measurable_fst)).pow_const 2).aestronglyMeasurable hTm.aemeasurable).2
    exact (hu' a).comp_fst (gaussianReal 0 1)
  · intro a
    apply (integrable_map_measure (((hy a).comp (measurable_fst.comp measurable_fst)).pow_const 2).aestronglyMeasurable hTm.aemeasurable).2
    exact (hy' a).comp_fst (gaussianReal 0 1)
  · rw [integrable_map_measure (by fun_prop) hTm.aemeasurable]
    exact hq.comp_fst (gaussianReal 0 1)
  · rw [integrable_map_measure (by fun_prop) hTm.aemeasurable]
    have hi := integrable_linear_combination_sq (ν := μ.prod (gaussianReal 0 1))
      (fun a : Option (Fin r) => a.elim (fun z : (E × ℝ) × ℝ => z.2) (fun a z => u a z.1.1))
      (fun a => a.elim 1 b)
      (fun a => by
        cases a with
        | none => exact measurable_snd.aestronglyMeasurable
        | some a => exact ((hu a).comp (measurable_fst.comp measurable_fst)).aestronglyMeasurable)
      (fun a => by
        cases a with
        | none => exact (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq.comp_snd μ
        | some a => exact (hu' a).comp_fst (gaussianReal 0 1))
    simpa only [T,Function.comp_def,Fintype.sum_option,Option.elim_none,Option.elim_some,one_mul] using hi

theorem ExponentialEmpiricalConcentration.nondegenerate_full_query
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
    (hgood : ∀ n h, h ∈ G n → (U n h)ᵀ*U n h=1 ∧ (U n h)ᵀ*Y n h=(Y n h)ᵀ*U n h)
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
    let c := fun a => ∫ x, u a x*g x ∂ν
    let s := ∫ x, residualRecipe u g c x^2 ∂ν
    let W := fun n (z : H n × ((Fin n × Fin n) → ℝ)) i =>
      Real.sqrt n*(completedMatrix (U n z.1) (Y n z.1) z.2 *ᵥ q n z.1) i
    ExponentialConvergence ρ (fun n h => (∑ i, R n h i^2)/(n:ℝ)) s ∧
    ExponentialEmpiricalConcentration
      (fun n => (ρ n).prod (standardArrayLaw (Fin n × Fin n)))
      (fun n z i => (((X n z.1 i,Real.sqrt n*q n z.1 i),W n z i),
        (completedMatrix (U n z.1) (Y n z.1) z.2 *ᵥ (fun j => g (X n z.1 j))) i))
      ((normalizedRecipeLaw ν u y g).map (fun z => (z, Real.sqrt s*z.2+∑ a, c a*y a z.1.1))) ∧
    ExponentialSquareTails ρ (fun n h i => Real.sqrt n*q n h i) ∧
    ExponentialSquareTails (fun n => (ρ n).prod (standardArrayLaw (Fin n × Fin n))) W ∧
    ExponentialSquareTails (fun n => (ρ n).prod (standardArrayLaw (Fin n × Fin n)))
      (fun n z i => (completedMatrix (U n z.1) (Y n z.1) z.2 *ᵥ (fun j => g (X n z.1 j))) i) := by
  dsimp only
  have h := hX.nondegenerate_query_step ρ ν X hXm r U Y hUm hU G hG hrare
    (fun n h hh => (hgood n h hh).1) u y g hK hu hy hg huT hyT hgT hui hyi hgi heu hey hs
  dsimp only at h
  let : IsProbabilityMeasure (normalizedRecipeLaw ν u y g) :=
    normalizedRecipeLaw_probability ν u y g (fun a => (hu a).continuous.measurable) hg.continuous.measurable
  have hm := normalizedRecipeLaw_moments ν u y g
    (fun a => (hu a).continuous.measurable) (fun a => (hy a).continuous.measurable)
    hg.continuous.measurable hui hyi hgi
  have hC : ExponentialConvergence ρ
      (fun n h a => (∑ i, u a (X n h i)*g (X n h i))/(n:ℝ))
      (fun a => ∫ x, u a x*g x ∂ν) := by
    apply ExponentialConvergence.pi_finite
    intro a
    exact hX.product_average (u a) g (hu a) hg (huT a) hgT (hui a) hgi
  have hh := h.2.1.unnormalized_query_assembly ρ X U Y u y g hK hy hyT heu hey G hrare
    hgood (fun a => ∫ x, u a x*g x ∂ν)
    (∫ x, residualRecipe u g (fun a => ∫ z, u a z*g z ∂ν) x^2 ∂ν)
    hC h.1 (normalizedRecipeLaw ν u y g) h.2.2.2 hm.2.1 hm.2.2.2
  exact ⟨h.1,hh.1,h.2.2.1,h.2.2.2,hh.2⟩

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise

end

end OAI
