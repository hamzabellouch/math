import OAI.Probability.SLE.Loewner.SlitChartDisplacement
import OAI.Probability.SLE.Loewner.CapacityRadiusBound

namespace OAI

/-! A common exterior half-disk controls all normalized charts of slits inside it. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology

namespace SLEExactGauge

lemma radiusHullInverse_map {R : ℝ} (hR : 0<R) {z : ℂ} (hz : z∈exteriorUpperRadius R) :
    radiusHullInverse R (radiusHullMap R z)=z :=
  (radiusHullMap_bijOn hR).injOn.leftInvOn_invFunOn hz

lemma SimpleSlitChart.exterior_comparison {p : C(unitInterval,ℂ)} (P : SimpleSlitChart p)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖≤R)
    {z : ℂ} (hz : z∈exteriorUpperRadius R) :
    (radiusHullMap R z).im≤(P.forward z).im ∧
      ‖P.forward z-radiusHullMap R z‖≤(R^2-P.capacity)/(radiusHullMap R z).im := by
  have hmap : MapsTo (radiusHullInverse R) upperHalfPlane (upperHalfPlane \ range p) := by
    intro w hw
    have hr := radiusHullInverse_mapsTo hR hw
    refine ⟨hr.2,?_⟩
    rintro ⟨t,ht⟩
    have hh := hp t
    rw [ht] at hh
    exact (not_le_of_gt hr.1) hh
  have hd := P.forward_differentiable.comp (radiusHullInverse_differentiableOn hR) hmap
  have hm := P.bijOn.mapsTo.comp hmap
  have hn := hydrodynamic_composition_ratio P.coefficient (radiusHullInverse_normalized hR)
  have hheight (w : ℂ) (hw : w∈upperHalfPlane) := normalized_halfPlane_height hd hm hn hw
  have hcoef := hydrodynamic_composition_coefficient P.coefficient (radiusHullMap_coefficient hR)
    (radiusHullInverse_normalized hR) (fun w hw => radiusHullMap_inverse hR hw)
  have hc : 0≤R^2-P.capacity := sub_nonneg.mpr (P.capacity_le_radius_sq hR hp)
  have hh := nonnegative_im_hydrodynamic_bound (hd.sub differentiableOn_id)
    (fun w hw => by
      change 0 ≤ (P.forward (radiusHullInverse R w)-w).im
      simpa only [comp_apply,sub_im] using sub_nonneg.mpr (hheight w hw)) hc
    (by
      change Tendsto (fun w : ℂ => w*(P.forward (radiusHullInverse R w)-w))
        (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 (-((R^2-P.capacity:ℝ):ℂ)))
      have he : -((R^2-P.capacity:ℝ):ℂ) = (P.capacity:ℂ)-(R:ℂ)^2 := by
        push_cast
        ring
      rw [he]
      exact hcoef)
    ((radiusHullMap_bijOn hR).mapsTo hz)
  have hle := hheight _ ((radiusHullMap_bijOn hR).mapsTo hz)
  change ‖P.forward (radiusHullInverse R (radiusHullMap R z))-radiusHullMap R z‖ ≤
    (R^2-P.capacity)/(radiusHullMap R z).im at hh
  change (radiusHullMap R z).im ≤ (P.forward (radiusHullInverse R (radiusHullMap R z))).im at hle
  rw [radiusHullInverse_map hR hz] at hh hle
  exact ⟨hle,hh⟩

end SLEExactGauge

end

end OAI
