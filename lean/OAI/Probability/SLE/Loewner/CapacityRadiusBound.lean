import OAI.Probability.SLE.Loewner.InitialCapacity
import OAI.Probability.SLE.Loewner.RadiusHullInverse

namespace OAI

/-! A finite slit contained in a disk of radius R has capacity at most
R squared, by comparison with the explicit half-disk hull. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology

namespace SLEExactGauge

lemma SimpleSlitChart.capacity_le_radius_sq {p : C(unitInterval,ℂ)} (P : SimpleSlitChart p)
    {R : ℝ} (hR : 0<R) (hp : ∀ u : unitInterval, ‖p u‖≤R) : P.capacity≤R^2 := by
  have hm : MapsTo (radiusHullInverse R) upperHalfPlane (upperHalfPlane \ range p) := by
    intro z hz
    have hh := radiusHullInverse_mapsTo hR hz
    refine ⟨hh.2,?_⟩
    rintro ⟨u,hu⟩
    have hn := hp u
    rw [hu] at hn
    linarith [hh.1]
  apply nested_hydrodynamic_coefficient_le P.forward_differentiable P.bijOn.mapsTo
    (radiusHullInverse_differentiableOn hR) hm P.coefficient
    (by simpa only [ofReal_pow] using radiusHullMap_coefficient hR)
    (radiusHullInverse_normalized hR)
  exact fun _ hz => radiusHullMap_inverse hR hz

lemma initialCapacity_le_radius_sq (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {R : ℝ} (hR : 0<R) (t : unitInterval)
    (hp : ∀ u ∈ Icc 0 t, ‖p u‖≤R) : initialCapacity p hi h0 hH t≤R^2 := by
  by_cases ht : t=0
  · simp only [ht,initialCapacity_zero]
    positivity
  rw [initialCapacity,dite_eq_right ht]
  apply SimpleSlitChart.capacity_le_radius_sq _ hR
  intro u
  have hm : initialSubarc p t u ∈ p '' Icc 0 t := by
    rw [← initialSubarc_range]
    exact mem_range_self u
  obtain ⟨v,hv,he⟩ := hm
  rw [← he]
  exact hp v hv

end SLEExactGauge

end

end OAI
