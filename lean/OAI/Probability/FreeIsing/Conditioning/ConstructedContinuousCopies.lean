import OAI.Probability.FreeIsing.Conditioning.ConstructedConditionalCopies
import OAI.Probability.FreeIsing.Stochastic.ContinuousCopyBrownian

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ConstructedContinuousCopies

open WienerSampler ContinuousObservationHistory ContinuousNoiseSplit

variable {ι Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem measurable_futureArray_of_eval (s : ℝ≥0) (W : Ω → ι → Path)
    (hW : ∀ i t, Measurable (fun ω => W ω i (s + t) - W ω i s)) :
    Measurable (fun ω => futureArray s (W ω)) := by
  apply Measurable.of_eval
  intro i
  apply measurable_path_of_eval
  intro t
  exact hW i t

theorem indepFun_continuous_future
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (W Y : Ω → ι → Path)
    (hW : ∀ i t, Measurable[F t] (fun ω => W ω i t))
    (hY : ∀ i t, Measurable[F t] (fun ω => Y ω i t))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω i => W ω i t - W ω i s) inferInstance) (F s) P)
    (s : ℝ≥0) :
    IndepFun (fun ω => (stoppedArray s (W ω), stoppedArray s (Y ω)))
      (fun ω => futureArray s (W ω)) P := by
  let X : ℝ≥0 → Ω → ι → ℝ := fun t ω i => W ω i t
  have hX (t : ℝ≥0) : Measurable[F t] (X t) := by
    let : MeasurableSpace Ω := F t
    exact Measurable.of_eval fun i => hW i t
  let mFuture := MeasurableSpace.comap
    (fun ω (t : Set.Ici s) => X t ω - X s ω) inferInstance
  have hRaw : @Measurable Ω (Set.Ici s → ι → ℝ) mFuture inferInstance
      (fun ω t => X t ω - X s ω) := comap_measurable _
  have hFut : @Measurable Ω (ι → Path) mFuture inferInstance
      (fun ω => futureArray s (W ω)) :=
    measurable_futureArray_of_eval (mΩ := mFuture) s W (fun i t =>
      (measurable_pi_apply i).comp
        ((measurable_pi_apply (⟨s + t, by change s ≤ s + t; exact le_self_add⟩ : Set.Ici s)).comp hRaw))
  have hPast : Measurable[F s]
      (fun ω => (stoppedArray s (W ω), stoppedArray s (Y ω))) :=
    (measurable_stoppedArray_of_eval (mΩ := F s) s W
      (fun i t ht => (hW i t).mono (F.mono ht) le_rfl)).prodMk
      (measurable_stoppedArray_of_eval (mΩ := F s) s Y
        (fun i t ht => (hY i t).mono (F.mono ht) le_rfl))
  have hi : Indep (F s) mFuture P :=
    FilteredFutureIndependence.indep_future (mΩ := mΩ) (P := P) hX hind s
  exact indep_of_indep_of_le (μ := P) hi hPast.comap_le hFut.comap_le

theorem exists_compatible_conditionalCopies [Countable ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (W Y : Ω → ι → Path)
    (hW : ∀ i t, Measurable[F t] (fun ω => W ω i t))
    (hY : ∀ i t, Measurable[F t] (fun ω => Y ω i t))
    (hB : ∀ i, IsPreBrownianReal (fun t ω => W ω i t) P)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω i => W ω i t - W ω i s) inferInstance) (F s) P) :
    ∃ (rho : Measure (ι → Path)) (eta : Kernel (ι → Path) (ι → Path)),
      IsProbabilityMeasure rho ∧ IsMarkovKernel eta ∧
      rho = P.map W ∧ rho ⊗ₘ eta = P.map (fun ω => (W ω, Y ω)) ∧
      (∀ i, IsBrownianReal
        (fun t (q : ContinuousCopyBrownian.Joint (ι := ι)) => q.1 i t)
        (rho ⊗ₘ (eta ×ₖ eta))) ∧
      (∀ i, Martingale
        (fun t (q : ContinuousCopyBrownian.Joint (ι := ι)) => q.1 i t)
        ContinuousCopyBrownian.joinedFiltration (rho ⊗ₘ (eta ×ₖ eta))) := by
  have hWm : Measurable W := Measurable.of_eval fun i =>
    measurable_path_of_eval (fun t => (hW i t).mono (F.le t) le_rfl)
  have hYm : Measurable Y := Measurable.of_eval fun i =>
    measurable_path_of_eval (fun t => (hY i t).mono (F.le t) le_rfl)
  let Z : Ω → (ι → Path) × (ι → Path) := fun ω => (W ω, Y ω)
  have hZ : Measurable Z := hWm.prodMk hYm
  let R := P.map Z
  have : IsProbabilityMeasure R := inferInstance
  let rho := R.fst
  let eta := R.condKernel
  have hrho : rho = P.map W := Measure.fst_map_prodMk hWm hYm
  have hdecomp : rho ⊗ₘ eta = R := Measure.disintegrate R eta
  have hBrho (i : ι) : IsPreBrownianReal (fun t (w : ι → Path) => w i t) rho := by
    rw [hrho]
    constructor
    intro I
    have hm : Measurable (fun w : ι → Path => I.restrict (fun t => w i t)) :=
      Measurable.of_eval fun t =>
        (continuous_eval_const t.1).measurable.comp (measurable_pi_apply i)
    refine ⟨hm.aemeasurable, ?_⟩
    rw [Measure.map_map hm hWm]
    exact (hB i).hasLaw I |>.map_eq
  have hOriginal (s : ℝ≥0) : IndepFun
      (fun q : (ι → Path) × (ι → Path) => (stoppedArray s q.1, stoppedArray s q.2))
      (fun q => futureArray s q.1) (rho ⊗ₘ eta) := by
    rw [hdecomp]
    apply ConstructedConditionalCopies.indepFun_map_of_comp hZ
      (((measurable_stoppedArray s).comp measurable_fst).prodMk
        ((measurable_stoppedArray s).comp measurable_snd))
      ((measurable_futureArray s).comp measurable_fst)
    exact indepFun_continuous_future P F W Y hW hY hind s
  exact ⟨rho, eta, inferInstance, inferInstance, hrho, hdecomp,
    (fun i => ContinuousCopyBrownian.isBrownian_commonNoise i rho (hBrho i) eta),
    (fun i => ContinuousCopyBrownian.commonNoise_martingale i rho (hBrho i) eta hOriginal)⟩

end Problem367.ConstructedContinuousCopies

end

end OAI
