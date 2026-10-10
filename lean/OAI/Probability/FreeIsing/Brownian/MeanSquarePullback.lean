import OAI.Probability.FreeIsing.Brownian.MeanSquareDescent

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Problem367.PredictableL2

theorem hasSum_toLp_comp_measurePreserving
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P)
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 P)
    {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    (hsum : HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y)) :
    HasSum (fun i => ((hf i).comp_measurePreserving hφ).toLp (f i ∘ φ))
      ((hY.comp_measurePreserving hφ).toLp (Y ∘ φ)) := by
  apply (hasSum_toLp_iff_meanSquare (fun i => f i ∘ φ)
    (fun i => (hf i).comp_measurePreserving hφ)
    (hY.comp_measurePreserving hφ)).mpr
  exact (BrownianGrid.meanSquare_limit_comp_iff hφ
    (fun s : Finset ι => (memLp_finsetSum s (fun i _ => hf i)).aestronglyMeasurable)
    hY.aestronglyMeasurable).mpr
    (tendsto_integral_sq_error_of_hasSum f hf hY hsum)

end Problem367.PredictableL2

end

end OAI
