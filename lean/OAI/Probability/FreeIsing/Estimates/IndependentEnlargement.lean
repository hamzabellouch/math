import OAI.Probability.FreeIsing.Estimates.PastCompatibility

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace Problem367

theorem martingale_independent_enlargement
    {Ω ι : Type*} [Preorder ι] {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ι m} {B : ι → Ω → ℝ}
    {mPast mSignal : MeasurableSpace Ω}
    (hPast : mPast ≤ m) (hSignal : mSignal ≤ m)
    (hFiltration : ∀ t, ℱ t ≤ mPast)
    (hIndep : Indep mPast mSignal μ)
    (hB : Martingale B ℱ μ) :
    Martingale B (ℱ ⊔ Filtration.const ι mSignal hSignal) μ := by
  constructor
  · intro t
    exact (hB.stronglyMeasurable t).mono le_sup_left
  · intro s t hst
    exact (condExp_sup_independent_future (hFiltration s) hPast hSignal hIndep
      ((hB.stronglyMeasurable t).mono (hFiltration t)) (hB.integrable t)).trans
      (hB.condExp_ae_eq hst)

end Problem367

end

end OAI
