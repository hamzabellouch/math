import Mathlib

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SmoothObstruction.CompactInvariant

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]

/-- The pushforward of the initial probability by the jth iterate. -/
noncomputable def iterateLaw (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X) (j : ℕ) : ProbabilityMeasure X :=
  ⟨(μ : Measure X).map (T^[j]),
    (Measure.isProbabilityMeasure_map_iff (hT.iterate j).measurable.aemeasurable).2
      inferInstance⟩

/-- Cesaro averages indexed by n+1 to keep the total mass equal to one even
at the first index. No ergodic theorem is used in their construction. -/
noncomputable def cesaro (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X) (n : ℕ) : ProbabilityMeasure X :=
  ⟨((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ j ∈ range (n + 1),
      (iterateLaw T hT μ j : Measure X), by
    apply isProbabilityMeasure_iff.mpr
    simp only [Measure.finsetSum_apply, Measure.smul_apply, measure_univ,
      sum_const, card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)⟩

lemma integral_iterateLaw (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X) (j : ℕ) (f : X →ᵇ ℝ) :
    ∫ x, f x ∂(iterateLaw T hT μ j : Measure X) = ∫ x, f ((T^[j]) x) ∂(μ : Measure X) := by
  exact integral_map (hT.iterate j).measurable.aemeasurable f.continuous.aestronglyMeasurable

lemma integral_cesaro (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X) (n : ℕ) (f : X →ᵇ ℝ) :
    ∫ x, f x ∂(cesaro T hT μ n : Measure X) =
      (∑ j ∈ range (n + 1), ∫ x, f ((T^[j]) x) ∂(μ : Measure X)) / (n + 1) := by
  change (∫ x, f x ∂(((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • _)) = _
  rw [integral_smul_measure, integral_finsetSum_measure (fun j _ => f.integrable _)]
  simp [integral_iterateLaw, ENNReal.toReal_add, div_eq_mul_inv, mul_comm]

lemma cesaro_integral_defect (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X) (n : ℕ) (f : X →ᵇ ℝ) :
    (∫ x, f (T x) ∂(cesaro T hT μ n : Measure X)) -
      (∫ x, f x ∂(cesaro T hT μ n : Measure X)) =
      ((∫ x, f ((T^[n + 1]) x) ∂(μ : Measure X)) - ∫ x, f x ∂(μ : Measure X)) / (n + 1) := by
  let g : X →ᵇ ℝ := f.compContinuous ⟨T, hT⟩
  change (∫ x, g x ∂(cesaro T hT μ n : Measure X)) - _ = _
  rw [integral_cesaro, integral_cesaro, ← sub_div, ← sum_sub_distrib]
  have heq (j : ℕ) : (∫ x, g ((T^[j]) x) ∂(μ : Measure X)) =
      ∫ x, f ((T^[j + 1]) x) ∂(μ : Measure X) := by
    simp only [g, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
      Function.iterate_succ_apply']
  simp only [heq]
  rw [sum_range_sub (fun j => ∫ x, f ((T^[j]) x) ∂(μ : Measure X))]
  simp

omit [BorelSpace X] in
lemma integral_iterate_bound (μ : ProbabilityMeasure X) (T : X → X)
    (j : ℕ) (f : X →ᵇ ℝ) :
    |∫ x, f ((T^[j]) x) ∂(μ : Measure X)| ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := (μ : Measure X))
    (f := fun x => f ((T^[j]) x)) (C := ‖f‖)
    (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm ((T^[j]) x)))
  simpa [Real.norm_eq_abs, measureReal_def] using h

lemma cesaro_integral_defect_bound (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X) (n : ℕ) (f : X →ᵇ ℝ) :
    |(∫ x, f (T x) ∂(cesaro T hT μ n : Measure X)) -
      (∫ x, f x ∂(cesaro T hT μ n : Measure X))| ≤ 2 * ‖f‖ / (n + 1) := by
  rw [cesaro_integral_defect, abs_div, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ |∫ x, f ((T^[n + 1]) x) ∂(μ : Measure X)| + |∫ x, f x ∂(μ : Measure X)| := abs_sub _ _
    _ ≤ _ := by
      have h₀ := integral_iterate_bound μ T 0 f
      simp only [Function.iterate_zero, id_eq] at h₀
      linarith [integral_iterate_bound μ T (n + 1) f]

lemma cesaro_integral_defect_tendsto (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X) (f : X →ᵇ ℝ) :
    Tendsto (fun n => (∫ x, f (T x) ∂(cesaro T hT μ n : Measure X)) -
      (∫ x, f x ∂(cesaro T hT μ n : Measure X))) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun (n : ℕ) => by
    simpa only [Real.norm_eq_abs] using (cesaro_integral_defect_bound T hT μ n f))
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * ‖f‖)
  simpa only [mul_zero, mul_one_div] using h

variable [MetrizableSpace X] [CompactSpace X]

omit [CompactSpace X] in
/-- Any weak limit of the Cesaro orbit averages is invariant. -/
theorem cesaro_limit_invariant (T : X → X) (hT : Continuous T)
    (μ ν : ProbabilityMeasure X) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (hlim : Tendsto ((cesaro T hT μ) ∘ φ) atTop (𝓝 ν)) :
    MeasurePreserving T (ν : Measure X) (ν : Measure X) := by
  refine ⟨hT.measurable, ?_⟩
  let ν' := ν.map T
  change (ν' : Measure X) = (ν : Measure X)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [show (ν' : Measure X) = (ν : Measure X).map T from rfl,
    integral_map hT.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  let g : X →ᵇ ℝ := f.compContinuous ⟨T, hT⟩
  have hg := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim g)
  have hf := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim f)
  have hzero := (cesaro_integral_defect_tendsto T hT μ f).comp hφ
  have heq : (∫ x, f (T x) ∂(ν : Measure X)) - (∫ x, f x ∂(ν : Measure X)) = 0 :=
    tendsto_nhds_unique (hg.sub hf) hzero
  exact sub_eq_zero.mp heq

/-- Compactness of probability measures provides a genuine invariant law.
This is the Krylov--Bogoliubov argument used twice in the manuscript. -/
theorem exists_invariant_probability [Nonempty X] (T : X → X) (hT : Continuous T) :
    ∃ μ : ProbabilityMeasure X, MeasurePreserving T (μ : Measure X) (μ : Measure X) := by
  let μ₀ : ProbabilityMeasure X := ⟨Measure.dirac (Classical.choice ‹Nonempty X›), inferInstance⟩
  obtain ⟨ν, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq (cesaro T hT μ₀)
  exact ⟨ν, cesaro_limit_invariant T hT μ₀ ν hφ.tendsto_atTop hlim⟩


/-- Real continuous test integrals embed probability laws into a locally
convex product space. This permits direct reuse of Mathlib's Krein--Milman
lemma, without an unproved ergodic-decomposition input. -/
noncomputable def testEmbedding (μ : ProbabilityMeasure X) : (X →ᵇ ℝ) → ℝ :=
  fun f => ∫ x, f x ∂(μ : Measure X)

omit [MetrizableSpace X] [CompactSpace X] in
lemma continuous_testEmbedding : Continuous (testEmbedding (X := X)) := by
  apply continuous_pi
  intro f
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

omit [CompactSpace X] in
lemma testEmbedding_injective : Function.Injective (testEmbedding (X := X)) := by
  intro μ ν h
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact congrFun h f

omit [CompactSpace X] in
lemma invariant_probabilities_closed (T : X → X) (hT : Continuous T) :
    IsClosed {μ : ProbabilityMeasure X | MeasurePreserving T (μ : Measure X) (μ : Measure X)} := by
  have h := isClosed_eq (ProbabilityMeasure.continuous_map hT) continuous_id
  convert h using 1
  ext μ
  exact ⟨fun hm => ProbabilityMeasure.toMeasure_injective hm.map_eq,
    fun hm => ⟨hT.measurable, congrArg ProbabilityMeasure.toMeasure hm⟩⟩

/-- Every continuous self-map of a nonempty compact metrizable Borel space
has an ergodic invariant probability law, obtained as an extreme point. -/
theorem exists_ergodic_probability [Nonempty X] (T : X → X) (hT : Continuous T) :
    ∃ μ : ProbabilityMeasure X, Ergodic T (μ : Measure X) := by
  let K : Set (ProbabilityMeasure X) :=
    {μ | MeasurePreserving T (μ : Measure X) (μ : Measure X)}
  have hK : IsCompact K := (invariant_probabilities_closed T hT).isCompact
  have hKn : K.Nonempty := exists_invariant_probability T hT
  obtain ⟨v, hv⟩ := (hK.image continuous_testEmbedding).extremePoints_nonempty
    (hKn.image testEmbedding)
  obtain ⟨μ, hμ, rfl⟩ := hv.1
  refine ⟨μ, Ergodic.of_mem_extremePoints ⟨⟨hμ, inferInstance⟩, ?_⟩⟩
  intro ν₁ hν₁ ν₂ hν₂ hseg
  let : IsProbabilityMeasure ν₁ := hν₁.2
  let : IsProbabilityMeasure ν₂ := hν₂.2
  let p₁ : ProbabilityMeasure X := ⟨ν₁, hν₁.2⟩
  let p₂ : ProbabilityMeasure X := ⟨ν₂, hν₂.2⟩
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  have ha₁ : a ≤ 1 := by rw [← hab]; exact le_add_right le_rfl
  have hb₁ : b ≤ 1 := by rw [← hab]; exact le_add_left le_rfl
  have hat : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ha₁
  have hbt : b ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hb₁
  have hreal : a.toReal + b.toReal = 1 := by
    rw [← ENNReal.toReal_add hat hbt, hab, ENNReal.toReal_one]
  have hseg' : testEmbedding μ ∈ openSegment ℝ (testEmbedding p₁) (testEmbedding p₂) := by
    refine ⟨a.toReal, b.toReal, ENNReal.toReal_pos ha.ne' hat,
      ENNReal.toReal_pos hb.ne' hbt, hreal, ?_⟩
    funext f
    change a.toReal * (∫ x, f x ∂ν₁) + b.toReal * (∫ x, f x ∂ν₂) = _
    rw [testEmbedding, ← heq,
      integral_add_measure ((f.integrable ν₁).smul_measure hat)
        ((f.integrable ν₂).smul_measure hbt), integral_smul_measure, integral_smul_measure]
    rfl
  have hemb := hv.2 ⟨p₁, hν₁.1, rfl⟩ ⟨p₂, hν₂.1, rfl⟩ hseg'
  exact congrArg ProbabilityMeasure.toMeasure (testEmbedding_injective hemb)

end SmoothObstruction.CompactInvariant

namespace SmoothObstruction.CompactInvariant
open MeasureTheory Filter Topology TopologicalSpace Set
open scoped BoundedContinuousFunction

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Probability measures lift through continuous surjections from a compact
metric space. Finite simple approximants avoid any selection assumption. -/
theorem exists_probability_lift (π : X → Y) (hπ : Continuous π)
    (hsur : Function.Surjective π) (μ : ProbabilityMeasure Y) :
    ∃ ν : ProbabilityMeasure X, (ν : Measure X).map π=(μ : Measure Y) := by
  classical
  have : Nonempty Y := nonempty_of_isProbabilityMeasure (μ : Measure Y)
  let y₀ : Y := Classical.choice inferInstance
  let a (n : ℕ) : SimpleFunc Y Y := SimpleFunc.approxOn id measurable_id Set.univ y₀ (Set.mem_univ _) n
  let s : Y → X := fun y => Classical.choose (hsur y)
  have hs (y : Y) : π (s y)=y := Classical.choose_spec (hsur y)
  let b (n : ℕ) : SimpleFunc Y X := (a n).map s
  let v (n : ℕ) : ProbabilityMeasure X := μ.map (b n)
  obtain ⟨ν,φ,hφ,hlim⟩ := CompactSpace.tendsto_subseq v
  refine ⟨ν,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hπ.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  let g : X →ᵇ ℝ := f.compContinuous ⟨π,hπ⟩
  have hν := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim g
  have hμ : Tendsto (fun n => ∫ y, f (a n y) ∂(μ : Measure Y)) atTop
      (𝓝 (∫ y, f y ∂(μ : Measure Y))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (f.continuous.measurable.comp (a n).measurable).aestronglyMeasurable)
      (integrable_const _)
      (fun n => Filter.Eventually.of_forall (fun y => f.norm_coe_le_norm (a n y)))
    exact Filter.Eventually.of_forall (fun y => f.continuous.continuousAt.tendsto.comp
      (SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ y₀) (by simp)))
  have he (n : ℕ) : (∫ x,g x ∂(v n : Measure X))=∫ y,f (a n y) ∂(μ : Measure Y) := by
    change (∫ x,g x ∂((μ : Measure Y).map (b n)))=_
    rw [integral_map (b n).measurable.aemeasurable g.continuous.aestronglyMeasurable]
    simp only [g,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,
      b,SimpleFunc.map_apply,hs]
  simp only [Function.comp_apply,he] at hν
  exact tendsto_nhds_unique hν (hμ.comp hφ.tendsto_atTop)


end SmoothObstruction.CompactInvariant

namespace SmoothObstruction.CompactInvariant
open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped BoundedContinuousFunction
variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The required stationary lift with exactly the prescribed marginal. This
uses compactness and actual finite probability approximants, not a chosen
stationary lift as an additional hypothesis. -/
theorem exists_invariant_lift (π : X → Y) (hπ : Continuous π)
    (hsur : Function.Surjective π) (T : X → X) (hT : Continuous T) (S : Y → Y)
    (hsem : Function.Semiconj π T S) (μ : ProbabilityMeasure Y)
    (hS : MeasurePreserving S (μ : Measure Y) (μ : Measure Y)) :
    ∃ ν : ProbabilityMeasure X, MeasurePreserving T (ν : Measure X) (ν : Measure X) ∧
      (ν : Measure X).map π=(μ : Measure Y) := by
  obtain ⟨ν₀,hν₀⟩ := exists_probability_lift π hπ hsur μ
  have hproj (j : ℕ) : (iterateLaw T hT ν₀ j : Measure X).map π=(μ : Measure Y) := by
    change ((ν₀ : Measure X).map (T^[j])).map π=_
    rw [Measure.map_map hπ.measurable (hT.iterate j).measurable]
    have he : π∘(T^[j])=(S^[j])∘π := funext (hsem.iterate_right j)
    rw [he,←Measure.map_map (hS.iterate j).measurable hπ.measurable,hν₀]
    exact (hS.iterate j).map_eq
  obtain ⟨ν,φ,hφ,hlim⟩ := CompactSpace.tendsto_subseq (cesaro T hT ν₀)
  refine ⟨ν,cesaro_limit_invariant T hT ν₀ ν hφ.tendsto_atTop hlim,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hπ.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  let g : X →ᵇ ℝ := f.compContinuous ⟨π,hπ⟩
  have he (j : ℕ) : (∫ x,g ((T^[j]) x) ∂(ν₀ : Measure X))=∫ y,f y ∂(μ : Measure Y) := by
    rw [←integral_iterateLaw T hT ν₀ j g,←hproj j,
      integral_map hπ.measurable.aemeasurable f.continuous.aestronglyMeasurable]
    rfl
  have hc (n : ℕ) : (∫ x,g x ∂(cesaro T hT ν₀ n : Measure X))=∫ y,f y ∂(μ : Measure Y) := by
    rw [integral_cesaro]
    simp only [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    field_simp
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim g
  simp only [Function.comp_apply,hc] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds


end SmoothObstruction.CompactInvariant

end

end OAI
