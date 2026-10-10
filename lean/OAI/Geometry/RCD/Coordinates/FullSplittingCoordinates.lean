import OAI.Geometry.RCD.Harmonic.ProductProjection
import OAI.Geometry.RCD.Metric.ApproximationRestriction
import OAI.Geometry.RCD.Coordinates.TransformationInput

namespace OAI

/-! # Coordinates from product almost splitting

Huang--Huang (2024), Theorem 2.9(2), supplies the product approximation
formulated by `LocalAlmostSplittingInput`. Sharp RCD packing removes its
residual factor without assuming ambient flatness.
-/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.full_splitting_coordinates {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hpublished : LocalAlmostSplittingInput hX)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (p : X) (r : ℝ), 0 < r → -ε ≤ K*r^2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (16*r) ε u v →
        IsPointedApproximation p 0 r (1/16) η (fun x => r⁻¹ • (v x-v p)) := by
  obtain ⟨δ,hδ,hproj⟩ := hX.product_projection_of_packing hn hη
  obtain ⟨ε₀,he₀,hproduct⟩ := hpublished hn (δ/3) (by positivity)
  let ε := min ε₀ (1/16)
  have he : 0 < ε := lt_min he₀ (by norm_num)
  refine ⟨ε,he,?_⟩
  intro p r hr hcurv u v hsplit
  have heε₀ : ε ≤ ε₀ := min_le_left _ _
  have he16 : ε ≤ 1/16 := min_le_right _ _
  have hc : -1 ≤ K*(4*r)^2 := by nlinarith only [hcurv,he16]
  obtain ⟨Z,dZ,z₀,w,hw⟩ := hproduct p r hr (by linarith only [hcurv,heε₀]) u v
    (hsplit.mono_error _ _ he.le heε₀)
  let : MetricSpace Z := dZ
  have hres := hw.restrict_radius hr (show (0:ℝ)≤1 by norm_num)
    (show (1:ℝ)≤2 by norm_num) (show 0 ≤ δ/3 by positivity)
  have hres' : IsPointedApproximation p (WithLp.toLp 2 (0,z₀)) r 1 δ
      (fun x => WithLp.toLp 2 (r⁻¹ • (v x-v p),w x)) := by
    simpa only [show 3*(δ/3)=δ by ring] using hres
  have hout := hproj Z dZ p z₀ r hr hc
    (fun x => WithLp.toLp 2 (r⁻¹ • (v x-v p),w x)) hres'
  exact hout

end RegularPointCoordinates

end

end OAI
