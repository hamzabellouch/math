import OAI.Probability.SLE.Geometry.WaypointRouteProbability

namespace OAI

/-! A uniform positive tube probability for any fixed-speed physical
route on the finite exit window. It is a consequence of the cited planar
Wiener support input and compactness of based Lipschitz routes. -/

noncomputable section
open Set Metric MeasureTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction

namespace SLEExactGauge.RibbonCoordinates
open Target

def basedPhysicalRoute (r : ℝ → ℂ) (hr : Continuous r) : unitInterval →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t => r (3 * (t : ℝ)) - r 0, by fun_prop⟩

lemma basedPhysicalRoute_zero (r : ℝ → ℂ) (hr : Continuous r) :
    basedPhysicalRoute r hr 0 = 0 := by
  change r (3 * (0 : ℝ)) - r 0 = 0
  simp only [mul_zero, sub_self]

lemma basedPhysicalRoute_lipschitz (r : ℝ → ℂ) (C : ℝ≥0) (hr : LipschitzWith C r) :
    LipschitzWith (3 * C) (basedPhysicalRoute r hr.continuous) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hh := hr.dist_le_mul (3 * (u : ℝ)) (3 * (v : ℝ))
  change dist (r (3 * (u : ℝ)) - r 0) (r (3 * (v : ℝ)) - r 0) ≤ _
  rw [dist_sub_right]
  have hd : dist (3 * (u : ℝ)) (3 * (v : ℝ)) = 3 * dist u v := by
    rw [Subtype.dist_eq, Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
    norm_num
  rw [hd] at hh
  convert hh using 1
  push_cast
  ring

theorem uniform_physical_route_tube_probability
    (hpublished : PublishedPlanarWienerUnitSupport)
    (W : WienerLaw) (hW : IsWiener W) (C : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ r : ℝ → ℂ, LipschitzWith C r →
      q ≤ (W.prod W) {b | ∀ t ∈ Icc (0 : ℝ) 3,
        dist (physicalUnitBrownianPath (r 0) b t) (r t) < ε} := by
  obtain ⟨q, hq, hbound⟩ := uniform_planarWiener_tube_probability hpublished W hW (3 * C) hε
  refine ⟨q, hq, fun r hr => ?_⟩
  refine (hbound (basedPhysicalRoute r hr.continuous)
    (basedPhysicalRoute_lipschitz r C hr) (basedPhysicalRoute_zero r hr.continuous)).trans
    (measure_mono ?_)
  intro b hb t ht
  let u : unitInterval := ⟨t / 3, by linarith [ht.1], by linarith [ht.2]⟩
  have hu : unitClipPoint (t / 3) = u := Subtype.ext (unitClip_of_mem u.property)
  have he : 3 * (u : ℝ) = t := by dsimp only [u]; ring
  have hh := hb u
  change dist (planarUnitPath b u) (r (3 * (u : ℝ)) - r 0) < ε at hh
  rw [he] at hh
  unfold physicalUnitBrownianPath
  rw [hu]
  rw [dist_eq_norm] at hh ⊢
  convert hh using 1
  congr 1
  ring

end SLEExactGauge.RibbonCoordinates

end

end OAI
