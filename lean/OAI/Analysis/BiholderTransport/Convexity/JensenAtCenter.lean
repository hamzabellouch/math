import Mathlib
import OAI.Analysis.BiholderTransport.Contact.CenterSupportFamily
import OAI.Analysis.BiholderTransport.Convexity.JensenAt

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section JensenAtCenter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.jensen_at_center_row (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) {Lv : ℝ≥0} (hv : LipschitzWith Lv v)
    (hdual : IsCostDualPair u v) {φ : ℝ → ℝ} (hφ : Continuous φ) (hmono : Monotone φ)
    {w : M → ℝ} {t l : ℝ} (ht : 0<t) (ht1 : t<1) {a c : M} {N : Set (Model n)}
    (J : JensenSamplesAt w (fun y=>φ (v y)) t a c N) (k : ℕ)
    (hd : HasDerivAt φ l (v (J.Y (J.z k)))) (hl : 0<l) (hl1 : l<1) :
    Nonempty (TrueCenterRow a u v φ (extChartAt 𝓘(ℝ,Model n) a (J.Y (J.z k)))
      ((extChartAt 𝓘(ℝ,Model n) a).symm (J.z k)) (1-t) l) := by
  have hsource := (J.samples k).1
  have hleft := (extChartAt 𝓘(ℝ,Model n) a).left_inv hsource
  have hx := (extChartAt 𝓘(ℝ,Model n) a).map_source hsource
  apply hmtw.actual_center_row hu hv hdual hφ hmono hx
  · rwa [hleft]
  · exact hl
  · exact hl1
  · linarith
  · linarith
  · rw [hleft]
    exact ((J.samples k).2.2.1 (J.Y (J.z k))).mpr rfl

end JensenAtCenter
end WeakMTWTransport

end
end

end OAI
