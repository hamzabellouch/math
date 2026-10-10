import OAI.Analysis.CircleDomains.Sobolev.RescaledBandEnergy
import OAI.Analysis.CircleDomains.Sobolev.PhysicalSobolevLipschitzCover

namespace OAI

/-! The original Sobolev energy pushed to the scalar graph. The local
capacity cost is bounded by its mass on an actual ambient graph ball. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

def sobolevGraph (u : EuclideanPlane → ℝ) (x : EuclideanPlane) : (ℝ × ℝ) × ℝ :=
  (euclideanPlaneCoordinates x,u x)

def sobolevGraphEnergy (u : EuclideanPlane → ℝ) (V : EuclideanPlane → EuclideanPlane) :
    Measure ((ℝ × ℝ) × ℝ) :=
  Measure.map (sobolevGraph u)
    (volume.withDensity (fun x => ENNReal.ofReal (1+(|V x 0|+|V x 1|)^2)))

lemma sobolevGraph_continuous {u : EuclideanPlane → ℝ} (hu : Continuous u) :
    Continuous (sobolevGraph u) := euclideanPlaneCoordinates.continuous.prodMk hu

lemma sobolev_graph_band_energy_le_ball {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (V : EuclideanPlane → EuclideanPlane) (a : EuclideanPlane) (t : ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ y in {y : EuclideanPlane | ‖y-a‖ ≤ 4*s ∧ |u y-t| ≤ 2*s},
      ENNReal.ofReal (1+(|V y 0|+|V y 1|)^2)) ≤
      sobolevGraphEnergy u V (closedBall (euclideanPlaneCoordinates a,t) (4*s)) := by
  rw [sobolevGraphEnergy, Measure.map_apply (sobolevGraph_continuous hu).measurable
    isClosed_closedBall.measurableSet,
    withDensity_apply _ (isClosed_closedBall.preimage (sobolevGraph_continuous hu)).measurableSet]
  apply lintegral_mono_set
  intro y hy
  change dist (euclideanPlaneCoordinates y,u y) (euclideanPlaneCoordinates a,t) ≤ 4*s
  rw [Prod.dist_eq]
  refine max_le ?_ ?_
  · have h := euclideanPlaneCoordinates_lipschitz.dist_le_mul y a
    simpa only [NNReal.coe_one,one_mul,dist_eq_norm] using h.trans (by simpa only [NNReal.coe_one,one_mul,dist_eq_norm] using hy.1)
  · rw [Real.dist_eq]
    exact hy.2.trans (by linarith)

end CircleDomainRigidity

end

end OAI
