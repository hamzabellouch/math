import OAI.Probability.FreeIsing.Conditioning.CutLevelConditionalMean
import OAI.Probability.FreeIsing.Estimates.BoundedAverageConcentration

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367

theorem integral_cond_fiber_le_of_condExp_le
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S]
    {μ : Measure Ω} [IsFiniteMeasure μ] {s : Ω → S} (hs : Measurable s)
    {f : Ω → ℝ} (hf : Integrable f μ) {C : ℝ}
    (hbound : ∀ᵐ ω ∂μ, (μ[f | MeasurableSpace.comap s inferInstance]) ω ≤ C)
    (a : S) (ha : μ (s ⁻¹' {a}) ≠ 0) :
    (∫ ω, f ω ∂μ[|s ⁻¹' {a}]) ≤ C := by
  have : (ae (μ.restrict (s ⁻¹' {a}))).NeBot :=
    ae_neBot.mpr (mt Measure.restrict_eq_zero.mp ha)
  have hCE := condExp_comap_eq_cond_on_fiber hs a hf
  have hB := ae_restrict_le (s := s ⁻¹' {a}) hbound
  obtain ⟨ω, hωCE, hωB⟩ := (hCE.and hB).exists
  exact hωCE.symm.le.trans hωB

theorem measureReal_le_of_cond_fibers
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [MeasurableSingletonClass S] [Countable S]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Ω → S} (hs : Measurable s)
    {E : Set Ω} (hE : MeasurableSet E) {C : ℝ}
    (hbound : ∀ a : S, μ (s ⁻¹' {a}) ≠ 0 → μ[|s ⁻¹' {a}].real E ≤ C) :
    μ.real E ≤ C := by
  have hCE : ∀ᵐ ω ∂μ,
      (μ[E.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap s inferInstance]) ω ≤ C := by
    apply ae_of_ae_restrict_fibers hs
    intro a
    by_cases ha : μ (s ⁻¹' {a}) = 0
    · rw [Measure.restrict_eq_zero.mpr ha]
      simp
    filter_upwards [condExp_indicator_comap_eq_cond_on_fiber hs a hE] with ω hω
    exact hω.le.trans (hbound a ha)
  have hint := integral_mono_ae integrable_condExp (integrable_const C) hCE
  rw [integral_condExp hs.comap_le] at hint
  simpa only [integral_indicator_const (1 : ℝ) hE, smul_eq_mul, mul_one,
    integral_const, probReal_univ, one_smul, one_mul] using hint

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem HasFreeIsingLaw.measure_cutLevel_average_ge_cond_le
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → ℝ)
    (hF : ∀ c, Measurable (F c)) (hbound : ∀ c p, 0 ≤ F c p ∧ F c p ≤ 1)
    (I : Finset (TreeShell d n)) (hI : I.Nonempty) {τ : ℝ} (hτ : 0 ≤ τ)
    (hmean : ∀ c ∈ I, (∫ z : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
      F c ((fun v => z.1 v.1), fun v => z.2 v.1) ∂μ.prod (Measure.infinitePi ν)) ≤ τ / 4)
    (s : TreeShell d n → IsingSpin)
    (hs : (μ.prod (Measure.infinitePi ν))
      {z | (fun c : TreeShell d n => z.1 c.1) = s} ≠ 0) :
    (μ.prod (Measure.infinitePi ν))[|{z | (fun c : TreeShell d n => z.1 c.1) = s}]
      {z | τ ≤ (∑ c ∈ I, F c ((fun v => z.1 v.1), fun v => z.2 v.1)) / (I.card : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(I.card : ℝ) * τ ^ 2 / 2)) := by
  let P := μ.prod (Measure.infinitePi ν)
  let S : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → TreeShell d n → IsingSpin :=
    fun z c => z.1 c.1
  let X := fun (c : TreeShell d n) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
    F c ((fun v => z.1 v.1), fun v => z.2 v.1)
  have hS : Measurable S := by fun_prop
  have hX : ∀ c, Measurable (X c) := fun c => (hF c).comp (by fun_prop)
  let : IsProbabilityMeasure ((μ.prod (Measure.infinitePi ν))[|
      {z | (fun c : TreeShell d n => z.1 c.1) = s}]) := cond_isProbabilityMeasure hs
  apply BoundedAverageConcentration.measure_average_ge_le
    (hμ.iIndepFun_cutLevel_observables_cond h0 h1 n ν F hF s hs) I hI hτ
  · intro c _
    exact (hX c).aemeasurable
  · intro c _
    exact Filter.Eventually.of_forall (fun z => hbound c _)
  · intro c hc
    have hi : Integrable (X c) P := by
      apply Integrable.of_bound (hX c).aestronglyMeasurable 1
      exact Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbound c _).1]
        exact (hbound c _).2)
    have hb := integral_cond_fiber_le_of_condExp_le hS hi
      (hμ.condExp_cutLevel_observable_le_two_integral h0 h1 n ν c (F c) (hF c)
        (hbound c)) s hs
    exact hb.trans (by linarith [hmean c hc])

theorem HasFreeIsingLaw.measure_cutLevel_average_ge_le
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → ℝ)
    (hF : ∀ c, Measurable (F c)) (hbound : ∀ c p, 0 ≤ F c p ∧ F c p ≤ 1)
    (I : Finset (TreeShell d n)) (hI : I.Nonempty) {τ : ℝ} (hτ : 0 ≤ τ)
    (hmean : ∀ c ∈ I, (∫ z : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
      F c ((fun v => z.1 v.1), fun v => z.2 v.1) ∂μ.prod (Measure.infinitePi ν)) ≤ τ / 4) :
    (μ.prod (Measure.infinitePi ν))
      {z | τ ≤ (∑ c ∈ I, F c ((fun v => z.1 v.1), fun v => z.2 v.1)) / (I.card : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(I.card : ℝ) * τ ^ 2 / 2)) := by
  let P := μ.prod (Measure.infinitePi ν)
  let S : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → TreeShell d n → IsingSpin :=
    fun z c => z.1 c.1
  have hS : Measurable S := by fun_prop
  have hsum : Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      ∑ c ∈ I, F c ((fun v => z.1 v.1), fun v => z.2 v.1)) :=
    Finset.measurable_fun_sum I (fun c _ => (hF c).comp (by fun_prop))
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  apply measureReal_le_of_cond_fibers hS (measurableSet_le measurable_const (hsum.div_const _))
  intro s hs
  have h := hμ.measure_cutLevel_average_ge_cond_le h0 h1 n ν F hF hbound I hI hτ hmean s hs
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr h |>.trans_eq
    (ENNReal.toReal_ofReal (Real.exp_pos _).le)

end Problem367

end

end OAI
