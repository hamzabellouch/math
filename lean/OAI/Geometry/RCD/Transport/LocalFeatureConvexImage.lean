import OAI.Geometry.RCD.Transport.LocalMidpointFeatures
import OAI.Geometry.RCD.Transport.ClosedMidpointConvex

namespace OAI

/-! # Compact convex images of the local distance coordinates -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MetricSpace Y] {q : Y}

def localDistanceFeature (q x : Y) : ball q (1:ℝ) → ℝ :=
  fun z => quadraticDistanceFeature q x z

theorem continuous_localDistanceFeature (q : Y) : Continuous (localDistanceFeature q) := by
  apply continuous_pi
  intro z
  dsimp only [localDistanceFeature,quadraticDistanceFeature]
  fun_prop

variable [ProperSpace Y]

theorem compact_local_feature_image (q : Y) (ρ : ℝ) :
    IsCompact (localDistanceFeature q '' closedBall q ρ) :=
  (isCompact_closedBall q ρ).image (continuous_localDistanceFeature q)

theorem LocalQuadraticMidpointGeometry.convex_local_feature_image
    (G : LocalQuadraticMidpointGeometry q) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρhalf : ρ < 1/2) :
    Convex ℝ (localDistanceFeature q '' closedBall q ρ) := by
  apply isClosed_convex_of_midpoints (compact_local_feature_image q ρ).isClosed
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  let x' : ball q (1/2:ℝ) := ⟨x,hx.trans_lt hρhalf⟩
  let y' : ball q (1/2:ℝ) := ⟨y,hy.trans_lt hρhalf⟩
  let z := G.mid x' y'
  have hz : (z:Y) ∈ closedBall q ρ := by
    have hh := G.quadratic x' y' q (by simp)
    change dist q (z:Y)^2 = (dist q x^2+dist q y^2)/2-dist x y^2/4 at hh
    simp only [dist_comm q] at hh
    have hx2 := pow_le_pow_left₀ dist_nonneg hx 2
    have hy2 := pow_le_pow_left₀ dist_nonneg hy 2
    apply (sq_le_sq₀ dist_nonneg hρ).mp
    nlinarith [sq_nonneg (dist x y)]
  refine ⟨z,hz,?_⟩
  exact G.feature_mid x' y'

end RegularPointCoordinates

end

end OAI
