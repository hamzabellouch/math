import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace Problem336.TiltLimit

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω]

def tiltedMean (μ : ProbabilityMeasure Ω) (h X : Ω → ℝ) : ℝ :=
  (∫ x, X x * Real.exp (h x) ∂(μ : Measure Ω)) /
    (∫ x, Real.exp (h x) ∂(μ : Measure Ω))

theorem tendsto_integral_continuous [CompactSpace Ω]
    {J : Type*} {l : Filter J} {μs : J → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hμ : Tendsto μs l (𝓝 μ)) {f : Ω → ℝ} (hf : Continuous f) :
    Tendsto (fun j => ∫ x, f x ∂(μs j : Measure Ω)) l
      (𝓝 (∫ x, f x ∂(μ : Measure Ω))) := by
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ
    (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩)

theorem integral_exp_pos [CompactSpace Ω] (μ : ProbabilityMeasure Ω)
    {h : Ω → ℝ} (hh : Continuous h) :
    0 < ∫ x, Real.exp (h x) ∂(μ : Measure Ω) := by
  apply MeasureTheory.integral_exp_pos
  exact (BoundedContinuousFunction.mkOfCompact ⟨_, (Real.continuous_exp.comp hh)⟩).integrable _

theorem tendsto_tiltedMean [CompactSpace Ω]
    {J : Type*} {l : Filter J} {μs : J → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hμ : Tendsto μs l (𝓝 μ)) {h X : Ω → ℝ} (hh : Continuous h) (hX : Continuous X) :
    Tendsto (fun j => tiltedMean (μs j) h X) l (𝓝 (tiltedMean μ h X)) := by
  exact (tendsto_integral_continuous hμ (hX.mul (Real.continuous_exp.comp hh))).div
    (tendsto_integral_continuous hμ (Real.continuous_exp.comp hh)) (ne_of_gt (integral_exp_pos μ hh))

theorem response_bound_of_tendsto [CompactSpace Ω]
    {J : Type*} {l : Filter J} [l.NeBot]
    {μs : J → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hμ : Tendsto μs l (𝓝 μ)) {h h' X : Ω → ℝ}
    (hh : Continuous h) (hh' : Continuous h') (hX : Continuous X) {C : ℝ}
    (hbound : ∀ᶠ j in l, |tiltedMean (μs j) h X - tiltedMean (μs j) h' X| ≤ C) :
    |tiltedMean μ h X - tiltedMean μ h' X| ≤ C := by
  exact le_of_tendsto
    ((tendsto_tiltedMean hμ hh hX).sub (tendsto_tiltedMean hμ hh' hX)).abs hbound

omit [TopologicalSpace Ω] [OpensMeasurableSpace Ω] in

theorem measurable_tiltedMean {A : Type*} [MeasurableSpace A]
    (μ : ProbabilityMeasure Ω) (h X : A → Ω → ℝ)
    (hh : Measurable (Function.uncurry h))
    (hX : Measurable (Function.uncurry X)) :
    Measurable (fun a => tiltedMean μ (h a) (X a)) := by
  exact ((hX.mul hh.exp).stronglyMeasurable.integral_prod_right).measurable.div
    (hh.exp.stronglyMeasurable.integral_prod_right).measurable

theorem tiltedMean_mem_Icc [CompactSpace Ω] (μ : ProbabilityMeasure Ω)
    {h X : Ω → ℝ} (hh : Continuous h) (hX : Continuous X)
    (hb : ∀ x, X x ∈ Set.Icc (0 : ℝ) 1) :
    tiltedMean μ h X ∈ Set.Icc (0 : ℝ) 1 := by
  have hd := integral_exp_pos μ hh
  have hi : Integrable (fun x => Real.exp (h x)) (μ : Measure Ω) :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, Real.continuous_exp.comp hh⟩).integrable _
  have hn : Integrable (fun x => X x * Real.exp (h x)) (μ : Measure Ω) :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, hX.mul (Real.continuous_exp.comp hh)⟩).integrable _
  constructor
  · exact div_nonneg (integral_nonneg (fun x => mul_nonneg (hb x).1 (Real.exp_pos _).le)) hd.le
  · apply (div_le_one₀ hd).2
    exact integral_mono hn hi (fun x => mul_le_of_le_one_left (Real.exp_pos _).le (hb x).2)

omit [TopologicalSpace Ω] [OpensMeasurableSpace Ω] in

theorem tiltedMean_map {Ω' : Type*} [MeasurableSpace Ω']
    (μ : ProbabilityMeasure Ω) {f : Ω → Ω'} (hf : Measurable f)
    {h X : Ω' → ℝ} (hh : Measurable h) (hX : Measurable X) :
    tiltedMean (μ.map f) h X =
      tiltedMean μ (fun x => h (f x)) (fun x => X (f x)) := by
  change (∫ x, X x * Real.exp (h x) ∂Measure.map f (μ : Measure Ω)) /
    (∫ x, Real.exp (h x) ∂Measure.map f (μ : Measure Ω)) = _
  unfold tiltedMean
  congr 1
  · exact integral_map_of_stronglyMeasurable hf (hX.mul hh.exp).stronglyMeasurable
  · exact integral_map_of_stronglyMeasurable hf hh.exp.stronglyMeasurable

variable {I : Type*}

def bit (b : Bool) : ℝ := if b then 1 else 0

theorem continuous_bit : Continuous bit := continuous_of_discreteTopology

def finiteEnergy (S : Finset I) (h : I → ℝ) (x : I → Bool) : ℝ :=
  ∑ i ∈ S, h i * bit (x i)

theorem continuous_finiteEnergy (S : Finset I) (h : I → ℝ) :
    Continuous (finiteEnergy S h) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (continuous_bit.comp (continuous_apply i))

def finiteTiltMean (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (h : I → ℝ) (e : I) : ℝ :=
  tiltedMean μ (finiteEnergy S h) (fun x => bit (x e))

variable [Countable I]

theorem tendsto_finiteTiltMean
    {J : Type*} {l : Filter J}
    {μs : J → ProbabilityMeasure (I → Bool)} {μ : ProbabilityMeasure (I → Bool)}
    (hμ : Tendsto μs l (𝓝 μ)) (S : Finset I) (h : I → ℝ) (e : I) :
    Tendsto (fun j => finiteTiltMean (μs j) S h e) l (𝓝 (finiteTiltMean μ S h e)) :=
  tendsto_tiltedMean hμ (continuous_finiteEnergy S h)
    (continuous_bit.comp (continuous_apply e))

theorem finiteTiltMean_response_bound_of_tendsto
    {J : Type*} {l : Filter J} [l.NeBot]
    {μs : J → ProbabilityMeasure (I → Bool)} {μ : ProbabilityMeasure (I → Bool)}
    (hμ : Tendsto μs l (𝓝 μ)) (S : Finset I) (h h' : I → ℝ) (e : I) {C : ℝ}
    (hbound : ∀ᶠ j in l,
      |finiteTiltMean (μs j) S h e - finiteTiltMean (μs j) S h' e| ≤ C) :
    |finiteTiltMean μ S h e - finiteTiltMean μ S h' e| ≤ C :=
  response_bound_of_tendsto hμ (continuous_finiteEnergy S h) (continuous_finiteEnergy S h')
    (continuous_bit.comp (continuous_apply e)) hbound

theorem finiteTiltMean_mem_Icc (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (h : I → ℝ) (e : I) :
    finiteTiltMean μ S h e ∈ Set.Icc (0 : ℝ) 1 := by
  apply tiltedMean_mem_Icc μ (continuous_finiteEnergy S h)
    (continuous_bit.comp (continuous_apply e))
  intro x
  cases hx : x e <;> simp [bit, hx]

omit [Countable I] in

theorem measurable_finitePosterior (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (e : I) :
    Measurable (fun p : ℝ × (I → ℝ) =>
      finiteTiltMean μ S (fun i => p.2 i - p.1 / 2) e) := by
  apply measurable_tiltedMean
  · change Measurable (fun q : (ℝ × (I → ℝ)) × (I → Bool) =>
      ∑ i ∈ S, (q.1.2 i - q.1.1 / 2) * bit (q.2 i))
    apply Finset.measurable_sum
    intro i hi
    have hfield : Measurable (fun q : (ℝ × (I → ℝ)) × (I → Bool) =>
        q.1.2 i - q.1.1 / 2) :=
      (((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).sub
        ((measurable_fst.comp measurable_fst).div_const 2))
    have hbit : Measurable (fun q : (ℝ × (I → ℝ)) × (I → Bool) => bit (q.2 i)) :=
      continuous_bit.measurable.comp ((measurable_pi_apply i).comp measurable_snd)
    exact hfield.mul hbit
  · change Measurable (fun q : (ℝ × (I → ℝ)) × (I → Bool) => bit (q.2 e))
    exact continuous_bit.measurable.comp ((measurable_pi_apply e).comp measurable_snd)

def reindex {J : Type*} (σ : I ≃ J) (x : I → Bool) : J → Bool :=
  fun j => x (σ.symm j)

omit [Countable I] in
theorem measurable_reindex {J : Type*} (σ : I ≃ J) : Measurable (reindex σ) := by
  exact Measurable.of_eval (fun j => measurable_pi_apply (σ.symm j))

omit [Countable I] in
theorem finiteEnergy_reindex {J : Type*} (σ : I ≃ J)
    (S : Finset I) (h : I → ℝ) (x : I → Bool) :
    finiteEnergy (S.map σ.toEmbedding) (fun j => h (σ.symm j)) (reindex σ x) =
      finiteEnergy S h x := by
  simp [finiteEnergy, reindex]

omit [Countable I] in

theorem finiteTiltMean_reindex {J : Type*} [Countable J] (σ : I ≃ J)
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (h : I → ℝ) (e : I) :
    finiteTiltMean (μ.map (reindex σ))
      (S.map σ.toEmbedding) (fun j => h (σ.symm j)) (σ e) =
      finiteTiltMean μ S h e := by
  have hm := tiltedMean_map μ (measurable_reindex σ)
    (continuous_finiteEnergy (S.map σ.toEmbedding) (fun j => h (σ.symm j))).measurable
    (show Measurable (fun x : J → Bool => bit (x (σ e))) from
      continuous_bit.measurable.comp (measurable_pi_apply (σ e)))
  simpa only [finiteTiltMean, finiteEnergy_reindex, reindex, Equiv.symm_apply_apply] using hm

end Problem336.TiltLimit

end

end OAI
