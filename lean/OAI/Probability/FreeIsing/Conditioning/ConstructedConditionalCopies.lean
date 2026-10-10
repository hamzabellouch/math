import OAI.Probability.FreeIsing.Estimates.FilteredFutureIndependence
import OAI.Probability.FreeIsing.Posterior.ContinuousObservationHistory

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ConstructedConditionalCopies

open WienerSampler ContinuousObservationHistory

theorem indepFun_map_of_comp {Ω Z A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {z : Ω → Z} (hz : Measurable z) {f : Z → A} {g : Z → B}
    (hf : Measurable f) (hg : Measurable g)
    (hind : IndepFun (f ∘ z) (g ∘ z) P) : IndepFun f g (P.map z) := by
  let : IsProbabilityMeasure (P.map z) := inferInstance
  rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable]
  rw [Measure.map_map (hf.prodMk hg) hz, Measure.map_map hf hz, Measure.map_map hg hz]
  exact hind.map_prod_eq_prod_map_map (hf.comp hz).aemeasurable (hg.comp hz).aemeasurable

theorem exists_compatible_conditionalCopies
    {ι Ω : Type*} [Countable ι] [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ι → ℝ)
    (hX : ∀ t, Measurable[F t] (X t))
    (hB : ∀ i, IsPreBrownianReal (fun t ω => X t ω i) P)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance) (F s) P)
    (Y : Ω → ι → Path) (hY : Measurable Y)
    (hYad : ∀ i t, Measurable[F t] (fun ω => Y ω i t)) :
    ∃ (rho : Measure (ℝ≥0 → ι → ℝ)) (eta : Kernel (ℝ≥0 → ι → ℝ) (ι → Path)),
      IsProbabilityMeasure rho ∧ IsMarkovKernel eta ∧
      rho = P.map (fun ω t => X t ω) ∧
      rho ⊗ₘ eta = P.map (fun ω => ((fun t => X t ω), Y ω)) ∧
      (∀ i, IsPreBrownianReal
        (fun t (q : (ℝ≥0 → ι → ℝ) × ((ι → Path) × (ι → Path))) => q.1 t i)
        (rho ⊗ₘ (eta ×ₖ eta))) ∧
      (∀ i, Martingale
        (fun t (q : (ℝ≥0 → ι → ℝ) × ((ι → Path) × (ι → Path))) => q.1 t i)
        ContinuousObservationHistory.joinedFiltration (rho ⊗ₘ (eta ×ₖ eta))) := by
  let W : Ω → ℝ≥0 → ι → ℝ := fun ω t => X t ω
  have hW : Measurable W := Measurable.of_eval fun t =>
    (hX t).mono (F.le t) le_rfl
  let Z : Ω → (ℝ≥0 → ι → ℝ) × (ι → Path) := fun ω => (W ω, Y ω)
  have hZ : Measurable Z := hW.prodMk hY
  let R := P.map Z
  have : IsProbabilityMeasure R := inferInstance
  let rho := R.fst
  let eta := R.condKernel
  have hrho : rho = P.map W := Measure.fst_map_prodMk hW hY
  have hdecomp : rho ⊗ₘ eta = R := Measure.disintegrate R eta
  have hBrho (i : ι) : IsPreBrownianReal (fun t (w : ℝ≥0 → ι → ℝ) => w t i) rho := by
    rw [hrho]
    constructor
    intro I
    have hm : Measurable (fun w : ℝ≥0 → ι → ℝ => I.restrict (fun t => w t i)) :=
      Measurable.of_eval fun t => (measurable_pi_apply i).comp (measurable_pi_apply t.1)
    refine ⟨hm.aemeasurable, ?_⟩
    rw [Measure.map_map hm hW]
    exact (hB i).hasLaw I |>.map_eq
  have hOriginal (s : ℝ≥0) : IndepFun
      (fun q : (ℝ≥0 → ι → ℝ) × (ι → Path) =>
        (PathSplit.pastPath s q.1, stoppedArray s q.2))
      (fun q => PathSplit.futureIncrements s q.1) (rho ⊗ₘ eta) := by
    rw [hdecomp]
    have hPast : Measurable[F s] (fun ω => stoppedArray s (Y ω)) :=
      measurable_stoppedArray_of_eval (mΩ := F s) s Y
        (fun i t ht => (hYad i t).mono (F.mono ht) le_rfl)
    apply indepFun_map_of_comp hZ
      (((PathSplit.measurable_pastPath s).comp measurable_fst).prodMk
        ((measurable_stoppedArray s).comp measurable_snd))
      ((PathSplit.measurable_futureIncrements s).comp measurable_fst)
    exact FilteredFutureIndependence.indepFun_past_and_observable_strict_future
      hX hind s hPast
  exact ⟨rho, eta, inferInstance, inferInstance, hrho, hdecomp,
    (fun i => ConditionalCopyArrayBrownian.isPreBrownian_commonNoise i rho (hBrho i) eta),
    (fun i => ContinuousObservationHistory.commonNoise_martingale i rho (hBrho i) eta hOriginal)⟩

end Problem367.ConstructedConditionalCopies

end

end OAI
