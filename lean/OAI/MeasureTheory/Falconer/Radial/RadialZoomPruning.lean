import OAI.MeasureTheory.Falconer.Radial.RadialZoom

namespace OAI

/-! # Pulling conditional radial pruning back to the unchanged original pair law -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_pruning_unzoom (μ ν : Measure (Space d)) [SFinite μ] [SFinite ν]
    {a : ℝ} (ha : 0 < a) (c : Space d)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (H : Set (Space d × Space d)) (hH : MeasurableSet H)
    (hsub : H ⊆ zoomPairSet (radialZoom a ha.ne' c) G)
    (θ : ℝ) (F E : ℝ≥0∞)
    (hdel : ((Measure.map (radialZoom a ha.ne' c) μ).prod
      (Measure.map (radialZoom a ha.ne' c) ν))
      (zoomPairSet (radialZoom a ha.ne' c) G \ H) ≤ E)
    (hbound : ∀ p ∈ H, radialCollisionMass (Measure.map (radialZoom a ha.ne' c) μ) θ p ≤ F) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ E ∧ ∀ p ∈ G', radialCollisionMass μ θ p ≤ F := by
  let e := radialZoom a ha.ne' c
  let G' := (Prod.map e e) ⁻¹' H
  have hG' : MeasurableSet G' := hH.preimage (e.measurable.prodMap e.measurable)
  refine ⟨G',hG',?_,?_,?_⟩
  · intro p hp
    exact (mem_zoomPairSet e G p.1 p.2).mp (hsub hp)
  · have he : (Prod.map e e) ⁻¹' (zoomPairSet e G \ H) = G \ G' := by
      ext p
      change ((e p.1,e p.2) ∈ zoomPairSet e G ∧ (e p.1,e p.2) ∉ H) ↔
        ((p.1,p.2) ∈ G ∧ (e p.1,e p.2) ∉ H)
      rw [mem_zoomPairSet]
    rw [← he,← Measure.map_apply (e.measurable.prodMap e.measurable)
      ((zoomPairSet_measurable e hG).diff hH),← Measure.map_prod_map μ ν e.measurable e.measurable]
    exact hdel
  · intro p hp
    have hh := hbound (e p.1,e p.2) hp
    rwa [radial_collision_zoom μ ha c p.1 p.2 θ] at hh

end Falconer

end OAI
