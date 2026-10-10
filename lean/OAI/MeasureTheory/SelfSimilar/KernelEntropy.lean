import OAI.MeasureTheory.SelfSimilar.WordAverage

namespace OAI

universe uα uβ uX

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory
open scoped BigOperators ENNReal

theorem finite_entropy_integral {X : Type uX} {β : Type uβ} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Finset β) (p : X → β → ℝ)
    (hm : ∀ b ∈ s, Measurable (fun y => p y b))
    (hp : ∀ b ∈ s, ∀ y, 0 ≤ p y b ∧ p y b ≤ 1) :
    (∫ y, ∑ b ∈ s, Real.negMulLog (p y b) ∂μ) ≤
      ∑ b ∈ s, Real.negMulLog (∫ y, p y b ∂μ) := by
  have hi (b) (hb : b ∈ s) : Integrable (fun y => p y b) μ :=
    (integrable_const (1 : ℝ)).mono' (hm b hb).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs,abs_of_nonneg (hp b hb y).1]; exact (hp b hb y).2))
  have hni (b) (hb : b ∈ s) : Integrable (fun y => Real.negMulLog (p y b)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (Real.continuous_negMulLog.measurable.comp (hm b hb)).aestronglyMeasurable
    filter_upwards [] with y
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.negMulLog_nonneg (hp b hb y).1 (hp b hb y).2)]
    exact (Real.negMulLog_le_one_sub_self (hp b hb y).1).trans (sub_le_self _ (hp b hb y).1)
  rw [integral_finsetSum s hni]
  apply Finset.sum_le_sum
  intro b hb
  exact Real.concaveOn_negMulLog.le_map_integral Real.continuous_negMulLog.continuousOn
    isClosed_Ici (Filter.Eventually.of_forall (fun y => (hp b hb y).1)) (hi b hb) (hni b hb)

theorem random_observation_entropy {X : Type uX} {α : Type uα} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (F : α → X → ℝ) (hF : ∀ i, Measurable (F i))
    (hm : ν=∑ i, ENNReal.ofReal (p i) • μ.map (F i))
    (f : ℝ → ℤ) (hf : Measurable f) (s : Finset ℤ)
    (hs : ∀ i, ∀ᵐ y ∂μ, f (F i y) ∈ s) :
    (∫ y, FiniteEntropy.observableEntropy Finset.univ p (fun i => f (F i y)) ∂μ) ≤ entropy ν f := by
  classical
  let K : X → ℤ → ℝ := fun y b => FiniteEntropy.mass Finset.univ p (fun i => f (F i y)) b
  have hk (y : X) (b : ℤ) : K y b=∑ i, if f (F i y)=b then p i else 0 := by
    simp only [K,FiniteEntropy.mass,Finset.sum_filter]
  have hmK (b : ℤ) : Measurable (fun y => K y b) := by
    simp_rw [hk]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.ite
      (measurableSet_eq_fun (hf.comp (hF i)) measurable_const) measurable_const)
  have hpK (y : X) (b : ℤ) : 0 ≤ K y b ∧ K y b ≤ 1 := by
    refine ⟨FiniteEntropy.mass_nonneg _ _ _ (fun i _ => hp i) _,?_⟩
    change (∑ i ∈ Finset.univ.filter (fun i => f (F i y)=b), p i) ≤ 1
    rw [← hp1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hp i)
  have hmi (i : α) : IsProbabilityMeasure (μ.map (F i)) :=
    (Measure.isProbabilityMeasure_map_iff (hF i).aemeasurable).2 inferInstance
  let := hmi
  have hsupport : ∀ᵐ x ∂ν, f x ∈ s := by
    rw [hm]
    rw [ae_iff]
    simp only [Measure.coe_finsetSum,Finset.sum_apply,Measure.smul_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hh : ∀ᵐ x ∂μ.map (F i), f x ∈ s :=
      (ae_map_iff (hF i).aemeasurable (hf (s.finite_toSet.measurableSet))).mpr (hs i)
    rw [ae_iff] at hh
    rw [hh,smul_zero]
  have hmasses (b : ℤ) : (∫ y, K y b ∂μ)=mass ν f b := by
    rw [mass_mixture ν (fun i => μ.map (F i)) p hp hm f]
    simp_rw [hk]
    have hint (i : α) : Integrable (fun y => if f (F i y)=b then p i else 0) μ := by
      have hh : MeasurableSet {y | f (F i y)=b} :=
        measurableSet_eq_fun (hf.comp (hF i)) (measurable_const (a := b))
      have h := (integrable_const (p i) : Integrable (fun _ : X => p i) μ).indicator hh
      exact h.congr (Filter.Eventually.of_forall (fun y => by
        rw [Set.indicator_apply]
        rfl))
    rw [integral_finsetSum Finset.univ (fun i _ => hint i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [mass_map μ _ (hF i) f hf]
    have hind : (fun y => if f (F i y)=b then p i else 0) =
        ({y | f (F i y)=b} : Set X).indicator (fun _ => p i) := by
          funext y
          rw [Set.indicator_apply]
          rfl
    rw [hind,integral_indicator_const (p i) (show MeasurableSet {y | f (F i y)=b} from
      measurableSet_eq_fun (hf.comp (hF i)) (measurable_const (a := b)))]
    simp only [smul_eq_mul,mass,Function.comp_apply,mul_comm]
  have he : (fun y => FiniteEntropy.observableEntropy Finset.univ p (fun i => f (F i y))) =ᵐ[μ]
      fun y => ∑ b ∈ s, Real.negMulLog (K y b) := by
    filter_upwards [ae_all_iff.mpr hs] with y hy
    exact FiniteEntropy.observableEntropy_on_superset Finset.univ s p _ (fun i _ => hy i)
  rw [integral_congr_ae he,entropy_eq_sum ν f s hsupport]
  simpa only [hmasses] using finite_entropy_integral μ s K (fun b _ => hmK b) (fun b _ y => hpK y b)

theorem random_observation_integrable {X : Type uX} {α : Type uα} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsProbabilityMeasure μ] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (f : α → X → ℤ) (hf : ∀ i, Measurable (f i)) (s : Finset ℤ)
    (hs : ∀ i, ∀ᵐ y ∂μ, f i y ∈ s) :
    Integrable (fun y => FiniteEntropy.observableEntropy Finset.univ p (fun i => f i y)) μ := by
  classical
  let K : X → ℤ → ℝ := fun y b => FiniteEntropy.mass Finset.univ p (fun i => f i y) b
  have hk (y : X) (b : ℤ) : K y b=∑ i, if f i y=b then p i else 0 := by
    simp only [K,FiniteEntropy.mass,Finset.sum_filter]
  have hmK (b : ℤ) : Measurable (fun y => K y b) := by
    simp_rw [hk]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.ite
      (measurableSet_eq_fun (hf i) measurable_const) measurable_const)
  have hpK (y : X) (b : ℤ) : 0 ≤ K y b ∧ K y b ≤ 1 := by
    refine ⟨FiniteEntropy.mass_nonneg _ _ _ (fun i _ => hp i) _,?_⟩
    change (∑ i ∈ Finset.univ.filter (fun i => f i y=b), p i) ≤ 1
    rw [← hp1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hp i)
  have hi (b : ℤ) : Integrable (fun y => Real.negMulLog (K y b)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (Real.continuous_negMulLog.measurable.comp (hmK b)).aestronglyMeasurable
    filter_upwards [] with y
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.negMulLog_nonneg (hpK y b).1 (hpK y b).2)]
    exact (Real.negMulLog_le_one_sub_self (hpK y b).1).trans (sub_le_self _ (hpK y b).1)
  apply (integrable_finsetSum s (fun b _ => hi b)).congr
  filter_upwards [ae_all_iff.mpr hs] with y hy
  exact (FiniteEntropy.observableEntropy_on_superset Finset.univ s p _ (fun i _ => hy i)).symm

end EntropyRateDimension.MeasureEntropy

end OAI
