import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeProbeEndpoints
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorBridgeComposition

namespace OAI

/-! # Exact cancellation for the source bridge at its Cartan pivot -/

namespace PolycyclicRecognition

variable {N D G : Type*} [Group N] [Group D] [Group G]

theorem probe_pivot_bridge_identity
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (S : MulAut N) (n i s k : N) (d : D) :
    (ι (coneProbeFirst S n i s) * κ d)⁻¹ * (ι (coneProbeSecond S n i k) * κ d) =
      ι (φ d⁻¹ (S (s⁻¹ * k))) := by
  have he : (ι (coneProbeFirst S n i s) * κ d)⁻¹ *
        (ι (coneProbeSecond S n i k) * κ d) =
      (κ d)⁻¹ * ι ((coneProbeFirst S n i s)⁻¹ * coneProbeSecond S n i k) * κ d := by
    rw [map_mul, map_inv]
    group
  rw [he, coneProbe_bridge]
  simpa only [map_inv, inv_inv] using (hc d⁻¹ (S (s⁻¹ * k))).symm

variable [PseudoMetricSpace G] [IsIsometricSMul G G]

/-- The common ideal probe and basepoint disappear from the bridge length. -/
theorem probe_pivot_bridge_distance
    (φ : D →* MulAut N) (ι : N →* G) (κ : D →* G)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (S : MulAut N) (n i s k : N) (d : D) (x : G) :
    dist (x * (ι (coneProbeFirst S n i s) * κ d))
      (x * (ι (coneProbeSecond S n i k) * κ d)) =
        dist 1 (ι (φ d⁻¹ (S (s⁻¹ * k)))) := by
  rw [dist_mul_left]
  let a := ι (coneProbeFirst S n i s) * κ d
  let b := ι (coneProbeSecond S n i k) * κ d
  have hd : dist a b = dist 1 (a⁻¹ * b) := by
    simpa only [inv_mul_cancel] using (dist_mul_left a⁻¹ a b).symm
  exact hd.trans (congrArg (dist (1 : G)) (probe_pivot_bridge_identity φ ι κ hc S n i s k d))

end PolycyclicRecognition

end OAI
