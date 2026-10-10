import OAI.Probability.FreeIsing.Factors.ContinuousRecovery

namespace OAI

noncomputable section

open MeasureTheory Filter TopologicalSpace
open scoped NNReal Topology

namespace Problem367.StoppedProcessTransport

variable {Ω Ω' ι E : Type*}

theorem stoppedProcess_pullback [Nonempty ι] [LinearOrder ι]
    (φ : Ω' → Ω) (X : ι → Ω → E) (τ : Ω → WithTop ι) :
    stoppedProcess (fun t => X t ∘ φ) (τ ∘ φ) =
      fun t => stoppedProcess X τ t ∘ φ := rfl

theorem stoppedValue_pullback [Nonempty ι]
    (φ : Ω' → Ω) (X : ι → Ω → E) (τ : Ω → WithTop ι) :
    stoppedValue (fun t => X t ∘ φ) (τ ∘ φ) = stoppedValue X τ ∘ φ := rfl

theorem isStoppingTime_pullback [Preorder ι]
    [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    {F : Filtration ι mΩ} {G : Filtration ι mΩ'}
    {φ : Ω' → Ω} (hφ : ∀ t, Measurable[G t, F t] φ)
    {τ : Ω → WithTop ι} (hτ : IsStoppingTime F τ) :
    IsStoppingTime G (τ ∘ φ) := by
  intro t
  exact (hφ t) (hτ t)

theorem stoppedValue_ae_eq_of_continuous
    [MeasurableSpace Ω] {P : Measure Ω}
    [TopologicalSpace ι] [SeparableSpace ι] [Nonempty ι]
    [TopologicalSpace E] [T2Space E]
    {X Y : ι → Ω → E}
    (hX : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (hXY : ∀ t, X t =ᵐ[P] Y t) (τ : Ω → WithTop ι) :
    stoppedValue X τ =ᵐ[P] stoppedValue Y τ := by
  filter_upwards [ae_eq_of_continuous_of_evaluation_ae_eq hX hY hXY] with ω hω
  exact congrFun hω (τ ω).untopA

theorem stoppedProcess_ae_eq_of_continuous
    [MeasurableSpace Ω] {P : Measure Ω}
    [TopologicalSpace ι] [SeparableSpace ι] [Nonempty ι] [LinearOrder ι]
    [TopologicalSpace E] [T2Space E]
    {X Y : ι → Ω → E}
    (hX : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (hXY : ∀ t, X t =ᵐ[P] Y t) (τ : Ω → WithTop ι) :
    (fun ω t => stoppedProcess X τ t ω) =ᵐ[P]
      (fun ω t => stoppedProcess Y τ t ω) := by
  filter_upwards [ae_eq_of_continuous_of_evaluation_ae_eq hX hY hXY] with ω hω
  funext t
  exact congrFun hω (min (t : WithTop ι) (τ ω)).untopA

theorem integral_stoppedProcess_sq_pullback
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [Nonempty ι] [LinearOrder ι]
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P) (X : ι → Ω → ℝ)
    (τ : Ω → WithTop ι) (t : ι)
    (hX : AEStronglyMeasurable (stoppedProcess X τ t) P) :
    (∫ ω, stoppedProcess (fun s => X s ∘ φ) (τ ∘ φ) t ω ^ 2 ∂Q) =
      ∫ ω, stoppedProcess X τ t ω ^ 2 ∂P := by
  change (∫ ω, stoppedProcess X τ t (φ ω) ^ 2 ∂Q) = _
  have hm : AEStronglyMeasurable (fun ω => stoppedProcess X τ t ω ^ 2) (Q.map φ) := by
    rw [hφ.map_eq]
    exact hX.pow 2
  simpa only [hφ.map_eq] using (integral_map hφ.aemeasurable hm).symm

theorem integral_stoppedProcess_sq_congr
    [MeasurableSpace Ω] {P : Measure Ω}
    [TopologicalSpace ι] [SeparableSpace ι] [Nonempty ι] [LinearOrder ι]
    {X Y : ι → Ω → ℝ}
    (hX : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (hXY : ∀ t, X t =ᵐ[P] Y t) (τ : Ω → WithTop ι) (t : ι) :
    (∫ ω, stoppedProcess X τ t ω ^ 2 ∂P) =
      ∫ ω, stoppedProcess Y τ t ω ^ 2 ∂P := by
  apply integral_congr_ae
  filter_upwards [stoppedProcess_ae_eq_of_continuous hX hY hXY τ] with ω hω
  exact congrArg (fun x : ℝ => x ^ 2) (congrFun hω t)

theorem integral_before_stop_pullback
    [mΩ : MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P)
    {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) {A : Ω → ℝ}
    (hA : AEStronglyMeasurable A P) (s : ℝ≥0) :
    (∫ ω, if (s : WithTop ℝ≥0) ≤ τ (φ ω) then A (φ ω) else 0 ∂Q) =
      ∫ ω, if (s : WithTop ℝ≥0) ≤ τ ω then A ω else 0 ∂P := by
  classical
  have hs : MeasurableSet {ω | (s : WithTop ℝ≥0) ≤ τ ω} :=
    F.le s _ (hτ.measurableSet_ge s)
  have hm : AEStronglyMeasurable
      (fun ω => if (s : WithTop ℝ≥0) ≤ τ ω then A ω else 0) (Q.map φ) := by
    rw [hφ.map_eq]
    apply (hA.indicator hs).congr
    exact Filter.Eventually.of_forall
      (fun ω => Set.indicator_apply {ω | (s : WithTop ℝ≥0) ≤ τ ω} A ω)
  simpa only [hφ.map_eq] using (integral_map hφ.aemeasurable hm).symm

theorem intervalIntegral_before_stop_pullback
    [mΩ : MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P)
    {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) {A : ℝ → Ω → ℝ}
    (hA : ∀ s, AEStronglyMeasurable (A s) P) (a b : ℝ) :
    (∫ s in a..b, ∫ ω,
      if (s.toNNReal : WithTop ℝ≥0) ≤ τ (φ ω) then A s (φ ω) else 0 ∂Q) =
      ∫ s in a..b, ∫ ω,
        if (s.toNNReal : WithTop ℝ≥0) ≤ τ ω then A s ω else 0 ∂P := by
  apply intervalIntegral.integral_congr
  intro s _
  exact integral_before_stop_pullback hφ hτ (hA s) s.toNNReal

theorem local_square_identity_congr
    [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : ℝ≥0 → Ω → ℝ}
    (hX : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (hXY : ∀ t, X t =ᵐ[P] Y t)
    {D E : ℝ → Ω → ℝ} (hDE : ∀ s, D s =ᵐ[P] E s)
    (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0)
    (hlocal : (∫ ω, stoppedProcess X τ t ω ^ 2 ∂P) =
      (∫ ω, X 0 ω ^ 2 ∂P) + ∫ s in (0 : ℝ)..(t : ℝ),
        ∫ ω, if (s.toNNReal : WithTop ℝ≥0) ≤ τ ω then D s ω else 0 ∂P) :
    (∫ ω, stoppedProcess Y τ t ω ^ 2 ∂P) =
      (∫ ω, Y 0 ω ^ 2 ∂P) + ∫ s in (0 : ℝ)..(t : ℝ),
        ∫ ω, if (s.toNNReal : WithTop ℝ≥0) ≤ τ ω then E s ω else 0 ∂P := by
  rw [← integral_stoppedProcess_sq_congr hX hY hXY τ t, hlocal]
  congr 1
  · apply integral_congr_ae
    exact (hXY 0).mono (fun ω hω => congrArg (fun x : ℝ => x ^ 2) hω)
  · apply intervalIntegral.integral_congr
    intro s _
    apply integral_congr_ae
    filter_upwards [hDE s] with ω hω
    simp only [hω]

end Problem367.StoppedProcessTransport

end

end OAI
