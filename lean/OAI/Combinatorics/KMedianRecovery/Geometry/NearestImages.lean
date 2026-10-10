import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestDistance

namespace OAI

namespace MetricKMedianRecovery.LeafTransfer
variable {A X : Type*} [PseudoMetricSpace X] [DecidableEq X]

lemma nearest_images (W : Finset A) (hW : W.Nonempty) (r s : A → X) (p : X)
    (eps : ℝ) (hshrink : ∀ a ∈ W, dist p (s a) ≤ dist p (r a))
    (hloss : ∀ a ∈ W, dist p (r a) ≤ dist p (s a)+eps) :
    nearestDistance p (W.image s) ≤ nearestDistance p (W.image r) ∧
    nearestDistance p (W.image r) ≤ nearestDistance p (W.image s)+eps := by
  have hr : (W.image r).Nonempty := hW.image r
  have hs : (W.image s).Nonempty := hW.image s
  constructor
  · obtain ⟨x,hx,he⟩ := nearestDistance_attained p (W.image r) hr
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    rw [he]
    exact (nearestDistance_le_mem p (W.image s) (s a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩)).trans
      (hshrink a ha)
  · obtain ⟨x,hx,he⟩ := nearestDistance_attained p (W.image s) hs
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    rw [he]
    exact (nearestDistance_le_mem p (W.image r) (r a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩)).trans
      (hloss a ha)

end MetricKMedianRecovery.LeafTransfer

end OAI
