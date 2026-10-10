import Mathlib
import OAI.Analysis.BiholderTransport.Contact.AEContacts
import OAI.Analysis.BiholderTransport.Volume.AemeasurableAeContinuous
import OAI.Analysis.BiholderTransport.Contact.ContactSelection

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section AESelection
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma contactSelection_aemeasurable {v : M → ℝ} (hv : Continuous v) :
    AEMeasurable (contactSelection hv) (metricVolume (M := M) n) := by
  apply aemeasurable_of_ae_continuousAt
  filter_upwards [cTransform_ae_unique_contact (n := n) hv] with x hx
  apply contact_selection_continuousAt (continuous_cTransform hv) hv (contactSelection_mem hv)
  intro y hy
  exact hx.unique hy (contactSelection_mem hv x)

end AESelection
end WeakMTWTransport

end

end

end

end OAI
