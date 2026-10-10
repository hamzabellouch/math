import OAI.Probability.FreeIsing.Estimates.UniformSampler
import OAI.Probability.FreeIsing.Factors.Transfer

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem isFactorOfIID_of_standardBorelNoise {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [Nonempty A] [StandardBorelSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν]
    (H : (TreeVertex d → A) → (TreeVertex d → IsingSpin))
    (hH : Measurable H)
    (hlaw : HasFreeIsingLaw theta
      (Measure.map H (Measure.infinitePi (fun _ : TreeVertex d => ν))))
    (heq : ∀ g : TreeAut d,
      ∀ᵐ W ∂Measure.infinitePi (fun _ : TreeVertex d => ν),
        H (relabel g W) = relabel g (H W)) :
    IsFactorOfIID d theta := by
  obtain ⟨ξ, hξ, hν⟩ := exists_uniform01_sampler ν
  exact isFactorOfIID_of_product_sampler ν ξ hξ hν H hH hlaw heq

end Problem367

end

end OAI
