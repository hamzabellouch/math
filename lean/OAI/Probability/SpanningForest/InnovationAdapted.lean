import OAI.Probability.SpanningForest.InnovationMartingale

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped NNReal Topology

namespace Problem336.Innovation

theorem measurable_stopped_observation {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → ι → ℝ)
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (hadapted : ∀ t i, Measurable[ℱ t] (fun ω => Y t ω i)) (T : ℝ≥0) :
    Measurable[(borel ℝ).prod (ℱ T)]
      (fun q : ℝ × Ω => Y (min q.1.toNNReal T) q.2) := by
  let : MeasurableSpace Ω := ℱ T
  apply Measurable.of_eval
  intro i
  apply measurable_uncurry_of_continuous_of_measurable (m := ℱ T)
    (u := fun s : ℝ => fun ω : Ω => Y (min s.toNNReal T) ω i)
  · intro ω
    exact (hcont ω i).comp (by fun_prop)
  · intro s
    exact (hadapted (min s.toNNReal T) i).mono
      (ℱ.mono (min_le_right _ _)) le_rfl

theorem stronglyMeasurable_integrated_observation_drift
    {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → ι → ℝ)
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (hadapted : ∀ t i, Measurable[ℱ t] (fun ω => Y t ω i))
    (b : ℝ≥0 → (ι → ℝ) → ℝ) (hb : Measurable (Function.uncurry b))
    (T : ℝ≥0) :
    StronglyMeasurable[ℱ T]
      (fun ω => ∫ s in (0 : ℝ)..T, b s.toNNReal (Y s.toNNReal ω)) := by
  let : MeasurableSpace Ω := ℱ T
  have htime : Measurable[(borel ℝ).prod (ℱ T)]
      (fun q : ℝ × Ω => min q.1.toNNReal T) := by
    exact (show Continuous (fun s : ℝ => min s.toNNReal T) by fun_prop).measurable.comp
      measurable_fst
  have hfield := measurable_stopped_observation ℱ Y hcont hadapted T
  have hstop : Measurable[(borel ℝ).prod (ℱ T)]
      (fun q : ℝ × Ω => b (min q.1.toNNReal T) (Y (min q.1.toNNReal T) q.2)) :=
    hb.comp (htime.prodMk hfield)
  have hint : StronglyMeasurable[ℱ T]
      (fun ω => ∫ s in Ioc (0 : ℝ) (T : ℝ),
        b (min s.toNNReal T) (Y (min s.toNNReal T) ω)) :=
    hstop.stronglyMeasurable.integral_prod_left'
  convert hint using 1
  funext ω
  calc
    (∫ s in (0 : ℝ)..T, b s.toNNReal (Y s.toNNReal ω)) =
        ∫ s in Ioc (0 : ℝ) (T : ℝ), b s.toNNReal (Y s.toNNReal ω) :=
      intervalIntegral.integral_of_le T.2
    _ = ∫ s in Ioc (0 : ℝ) (T : ℝ),
        b (min s.toNNReal T) (Y (min s.toNNReal T) ω) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      dsimp only
      rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hs.2)]

theorem stronglyAdapted_observation_innovation
    {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → ι → ℝ)
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (hadapted : ∀ t i, Measurable[ℱ t] (fun ω => Y t ω i))
    (b : ℝ≥0 → (ι → ℝ) → ℝ) (hb : Measurable (Function.uncurry b))
    (i : ι) :
    StronglyAdapted ℱ (fun t ω => Y t ω i -
      ∫ s in (0 : ℝ)..t, b s.toNNReal (Y s.toNNReal ω)) := by
  intro t
  exact (hadapted t i).stronglyMeasurable.sub
    (stronglyMeasurable_integrated_observation_drift ℱ Y hcont hadapted b hb t)

theorem measurable_observation_field {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → ι → ℝ)
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (hadapted : ∀ t i, Measurable[ℱ t] (fun ω => Y t ω i)) :
    Measurable (fun q : ℝ × Ω => Y q.1.toNNReal q.2) := by
  apply Measurable.of_eval
  intro i
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun s : ℝ => fun ω : Ω => Y s.toNNReal ω i)
  · intro ω
    exact (hcont ω i).comp (by fun_prop)
  · intro s
    exact (hadapted s.toNNReal i).mono (ℱ.le _) le_rfl

theorem martingale_borel_observation
    {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    (Y : ℝ≥0 → Ω → ι → ℝ)
    (hcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (hadapted : ∀ t i, Measurable[ℱ t] (fun ω => Y t ω i))
    (i : ι) (X : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hobs : ∀ t ω, Y t ω i = (t : ℝ) * X ω + B t ω)
    (hX : Integrable X P) (hB : ∀ t, Integrable (B t) P)
    (b : ℝ≥0 → (ι → ℝ) → ℝ) (hb : Measurable (Function.uncurry b))
    {C : ℝ} (hbound : ∀ t y, ‖b t y‖ ≤ C)
    (hposterior : ∀ t : ℝ≥0, (fun ω => b t (Y t ω)) =ᵐ[P] P[X | ℱ t])
    (hnoise : ∀ u v, u ≤ v → ∀ A : Set Ω, MeasurableSet[ℱ u] A →
      (∫ ω in A, (B v ω - B u ω) ∂P) = 0) :
    Martingale (fun t ω => Y t ω i -
      ∫ s in (0 : ℝ)..t, b s.toNNReal (Y s.toNNReal ω)) ℱ P := by
  let bt : ℝ → Ω → ℝ := fun s ω => b s.toNNReal (Y s.toNNReal ω)
  have hbt : Measurable (Function.uncurry bt) :=
    hb.comp ((show Measurable (fun q : ℝ × Ω => q.1.toNNReal) by fun_prop).prodMk
      (measurable_observation_field ℱ Y hcont hadapted))
  have hbnd : ∀ t ω, ‖bt t ω‖ ≤ C := fun t ω => hbound _ _
  have hpost : ∀ t : ℝ≥0, bt t =ᵐ[P] P[X | ℱ t] := by
    intro t
    simpa only [bt, Real.toNNReal_coe] using hposterior t
  have heq : nnInnovation X B bt = (fun t ω => Y t ω i -
      ∫ s in (0 : ℝ)..t, b s.toNNReal (Y s.toNNReal ω)) := by
    funext t ω
    rw [nnInnovation_apply, hobs]
  have hstrong : StronglyAdapted ℱ (nnInnovation X B bt) := by
    rw [heq]
    exact stronglyAdapted_observation_innovation ℱ Y hcont hadapted b hb i
  rw [← heq]
  exact martingale_nnInnovation P ℱ hX hB hbt hbnd hpost hstrong hnoise

end Problem336.Innovation

end

end OAI
