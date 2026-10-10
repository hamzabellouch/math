import Mathlib
import OAI.Probability.ThreeStateClauses.CompactLimits

namespace OAI

/-! Observed Mixtures. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

variable {X : Type*} [MeasurableSpace X]

def mixtureProbability (ρ : PMF ℕ) (P : ℕ → ProbabilityMeasure X) : ProbabilityMeasure X :=
  ⟨Measure.sum (fun n ↦ ρ n • (P n).toMeasure), ⟨by
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simpa only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] using ρ.tsum_coe⟩⟩

lemma integral_mixtureProbability (ρ : PMF ℕ) (P : ℕ → ProbabilityMeasure X)
    {f : X → ℝ} (hf : Integrable f (mixtureProbability ρ P).toMeasure) :
    (∫ x, f x ∂(mixtureProbability ρ P).toMeasure) =
      ∑' n, (ρ n).toReal*(∫ x, f x ∂(P n).toMeasure) := by
  rw [show (mixtureProbability ρ P).toMeasure = Measure.sum (fun n ↦ ρ n • (P n).toMeasure) from rfl,
    integral_sum_measure hf]
  simp only [integral_smul_measure, smul_eq_mul]

lemma pmf_hasSum_real (ρ : PMF ℕ) : HasSum (fun n ↦ (ρ n).toReal) 1 := by
  have hs := ENNReal.summable_toReal ρ.tsum_coe_ne_top
  convert hs.hasSum using 1
  rw [← ENNReal.tsum_toReal_eq (fun n ↦ ρ.apply_ne_top n), ρ.tsum_coe]
  norm_num

lemma mixture_balanced (ρ : PMF ℕ) (Q : ℕ → Law) (i : Fin 3) :
    (∫ m, m.1 i ∂(mixtureProbability ρ (fun n ↦ (Q n).probability)).toMeasure) = 1 := by
  rw [integral_mixtureProbability _ _ (compact_integrable (continuous_coordinate i))]
  simp only [Law.balanced, mul_one]
  exact (pmf_hasSum_real ρ).tsum_eq

lemma mixture_symmetric (ρ : PMF ℕ) (Q : ℕ → Law) (σ : Equiv.Perm (Fin 3)) :
    MeasurePreserving (permute σ) (mixtureProbability ρ (fun n ↦ (Q n).probability)).toMeasure
      (mixtureProbability ρ (fun n ↦ (Q n).probability)).toMeasure := by
  refine ⟨(continuous_permute σ).measurable, ?_⟩
  change Measure.map _ (Measure.sum _) = Measure.sum _
  rw [Measure.map_sum (continuous_permute σ).measurable.aemeasurable]
  congr 1; funext n
  rw [Measure.map_smul _ (continuous_permute σ).measurable.aemeasurable,
    (Q n).symmetric σ |>.map_eq]

def mixtureLaw (ρ : PMF ℕ) (Q : ℕ → Law) : Law where
  probability := mixtureProbability ρ (fun n ↦ (Q n).probability)
  balanced := mixture_balanced ρ Q
  symmetric := mixture_symmetric ρ Q

def offspringLaw (ρ : PMF ℕ) (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) : Law :=
  mixtureLaw ρ (finiteLaw Q hl₀ hl₁)

lemma mixture_integrable (ρ : PMF ℕ) (P : ℕ → ProbabilityMeasure X) {f : X → ℝ}
    (hf : ∀ n, Integrable f (P n).toMeasure)
    (hs : Summable (fun n ↦ (ρ n).toReal*(∫ x, |f x| ∂(P n).toMeasure))) :
    Integrable f (mixtureProbability ρ P).toMeasure := by
  apply integrable_sum_measure
  · intro n; exact (hf n).smul_measure (ρ.apply_ne_top n)
  · simpa only [integral_smul_measure, smul_eq_mul, Real.norm_eq_abs] using hs

variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]

lemma mixtureProbability_tendsto {ι : Type*} {F : Filter ι} (ρ : PMF ℕ)
    {P : ι → ℕ → ProbabilityMeasure X} {R : ℕ → ProbabilityMeasure X}
    (hP : ∀ n, Tendsto (fun i ↦ P i n) F (𝓝 (R n))) :
    Tendsto (fun i ↦ mixtureProbability ρ (P i)) F (𝓝 (mixtureProbability ρ R)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  simp_rw [integral_mixtureProbability _ _ (compact_integrable f.continuous)]
  apply tendsto_tsum_of_dominated_convergence ((pmf_hasSum_real ρ).summable.mul_right ‖f‖)
  · intro n
    exact tendsto_const_nhds.mul ((probability_continuous_integral f.continuous).tendsto (R n) |>.comp (hP n))
  · exact Filter.Eventually.of_forall (fun i n ↦ by
      rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact (norm_integral_le_integral_norm _).trans (by
        exact (integral_mono (compact_integrable f.continuous.norm) (integrable_const _)
          (fun x ↦ f.norm_coe_le_norm x)).trans_eq (by simp)))

lemma offspringLaw_tendsto {ι : Type*} {F : Filter ι} (ρ : PMF ℕ) {Q : ι → Law} {R : Law}
    {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (hQ : Tendsto (fun i ↦ (Q i).probability) F (𝓝 R.probability)) :
    Tendsto (fun i ↦ (offspringLaw ρ (Q i) hl₀ hl₁).probability) F
      (𝓝 (offspringLaw ρ R hl₀ hl₁).probability) :=
  mixtureProbability_tendsto ρ (fun n ↦ finiteProbability_tendsto hQ hl₀ hl₁ n)

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

variable {α : ℕ → Type*}

def sigmaPMF (ρ : PMF ℕ) (p : ∀ n, PMF (α n)) : PMF (Sigma α) :=
  ⟨fun z ↦ ρ z.1*p z.1 z.2, ENNReal.summable.hasSum_iff.2 (by
    rw [ENNReal.tsum_sigma']
    simp only [ENNReal.tsum_mul_left]
    have hs (n : ℕ) : (∑' a, p n a) = 1 := (p n).tsum_coe
    simp only [hs, mul_one]
    exact ρ.tsum_coe)⟩

@[simp] lemma sigmaPMF_apply (ρ : PMF ℕ) (p : ∀ n, PMF (α n)) (n : ℕ) (a : α n) :
    sigmaPMF ρ p ⟨n,a⟩ = ρ n*p n a := rfl

lemma sigmaPMF_eq_bind (ρ : PMF ℕ) (p : ∀ n, PMF (α n)) :
    sigmaPMF ρ p = ρ.bind (fun n ↦ (p n).map (Sigma.mk n)) := by
  classical
  apply PMF.ext
  rintro ⟨n,a⟩
  rw [PMF.bind_apply, tsum_eq_single n]
  · simp [PMF.map_apply]
  · intro m hm
    have hn : n ≠ m := Ne.symm hm
    simp [PMF.map_apply, hn]

lemma sigmaPMF_bind {β : Type*} (ρ : PMF ℕ) (p : ∀ n, PMF (α n))
    (K : Sigma α → PMF β) :
    (sigmaPMF ρ p).bind K = ρ.bind (fun n ↦ (p n).bind (fun a ↦ K ⟨n,a⟩)) := by
  rw [sigmaPMF_eq_bind, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]

lemma sigmaPMF_map {β : Type*} (ρ : PMF ℕ) (p : ∀ n, PMF (α n))
    (T : Sigma α → β) :
    (sigmaPMF ρ p).map T = ρ.bind (fun n ↦ (p n).map (fun a ↦ T ⟨n,a⟩)) :=
  sigmaPMF_bind ρ p (fun z ↦ PMF.pure (T z))

lemma sigmaPMF_bind_components {β : ℕ → Type*} (ρ : PMF ℕ) (p : ∀ n, PMF (α n))
    (K : ∀ n, α n → PMF (β n)) :
    (sigmaPMF ρ p).bind (fun z ↦ (K z.1 z.2).map (Sigma.mk z.1)) =
      sigmaPMF ρ (fun n ↦ (p n).bind (K n)) := by
  rw [sigmaPMF_bind, sigmaPMF_eq_bind]
  simp only [PMF.map_bind]

lemma discreteSigma_marginal (ρ : PMF ℕ) (p : ∀ n, Spin → PMF (α n)) :
    discreteMarginal (fun i ↦ sigmaPMF ρ (fun n ↦ p n i)) =
      sigmaPMF ρ (fun n ↦ discreteMarginal (p n)) := by
  apply PMF.ext
  rintro ⟨n,a⟩
  simp only [discreteMarginal_apply, sigmaPMF_apply, div_eq_mul_inv]
  ring

lemma discreteSigma_weight (ρ : PMF ℕ) (p : ∀ n, Spin → PMF (α n)) (n : ℕ) (a : α n) :
    discreteWeight (fun i ↦ sigmaPMF ρ (fun n ↦ p n i)) ⟨n,a⟩ =
      (ρ n).toReal*discreteWeight (p n) a := by
  simp only [discreteWeight, sigmaPMF_apply, ENNReal.toReal_mul]
  exact avg_mul _ _

lemma discreteSigma_message (ρ : PMF ℕ) (p : ∀ n, Spin → PMF (α n))
    (n : ℕ) (a : α n) (hρ : (ρ n).toReal ≠ 0) :
    discreteMessage (fun i ↦ sigmaPMF ρ (fun n ↦ p n i)) ⟨n,a⟩ = discreteMessage (p n) a := by
  by_cases ha : discreteWeight (p n) a = 0
  · simp only [discreteMessage, discreteSigma_weight, ha, mul_zero, dite_true]
  · apply Subtype.ext
    funext i
    rw [discrete_coord (by rw [discreteSigma_weight]; exact mul_ne_zero hρ ha),
      discrete_coord ha, sigmaPMF_apply, ENNReal.toReal_mul, discreteSigma_weight]
    exact mul_div_mul_left _ _ hρ

section Measures
variable [∀ n, Countable (α n)] [∀ n, MeasurableSpace (α n)]
  [∀ n, MeasurableSingletonClass (α n)]

instance sigmaMeasurableSingleton : MeasurableSingletonClass (Sigma α) := by
  constructor
  intro z
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet ((Sigma.mk n) ⁻¹' {z})
  exact Set.Countable.measurableSet (Set.to_countable _)

lemma integral_sigmaPMF (ρ : PMF ℕ) (p : ∀ n, PMF (α n)) {f : Sigma α → ℝ} {B : ℝ}
    (hf : ∀ a, |f a| ≤ B) :
    (∫ a, f a ∂(sigmaPMF ρ p).toMeasure) =
      ∑' n, (ρ n).toReal*(∫ a, f ⟨n,a⟩ ∂(p n).toMeasure) := by
  rw [sigmaPMF_eq_bind, pmf_measure_bind, integral_sum_measure]
  · simp only [integral_smul_measure, smul_eq_mul, integral_pmf_map]
  · rw [← pmf_measure_bind]
    exact pmf_bounded_integrable _ hf

lemma discreteSigma_probability (ρ : PMF ℕ) (p : ∀ n, Spin → PMF (α n)) :
    discreteProbability (fun i ↦ sigmaPMF ρ (fun n ↦ p n i)) =
      mixtureProbability ρ (fun n ↦ discreteProbability (p n)) := by
  apply probability_ext_continuous
  intro f hf
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hbf (m : Message) : |f m| ≤ B := by simpa only [Real.norm_eq_abs] using hB m (mem_univ m)
  rw [integral_discreteProbability _ hf.measurable, discreteSigma_marginal,
    integral_sigmaPMF ρ _ (fun z ↦ hbf _),
    integral_mixtureProbability _ _ (compact_integrable hf)]
  apply tsum_congr
  intro n
  rw [integral_discreteProbability _ hf.measurable]
  by_cases hρ : (ρ n).toReal = 0
  · simp [hρ]
  · simp_rw [discreteSigma_message ρ p n _ hρ]

end Measures
end ThreeState.TreeClauses.Experiment

end

end OAI
