import OAI.Geometry.CylinderCovering.Radial.SectorWeighted

namespace OAI

open Set MeasureTheory

noncomputable section

namespace AngularCaps

private def pairPlaneEquiv : (ℝ × ℝ) ≃ᵐ EuclideanSpace ℝ (Fin 2) :=
  (MeasurableEquiv.finTwoArrow (α := ℝ)).symm.trans
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

theorem pairToPlane_measurableEmbedding : MeasurableEmbedding pairToPlane :=
  pairPlaneEquiv.measurableEmbedding

theorem pairToPlane_measurePreserving : MeasurePreserving pairToPlane volume volume :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm

theorem continuous_pairToPlane : Continuous pairToPlane := by
  unfold pairToPlane
  fun_prop

theorem pairToPlane_volume (S : Set (ℝ × ℝ)) :
    volume (pairToPlane '' S) = volume S := by
  rw [← pairToPlane_measurePreserving.measure_preimage_emb pairToPlane_measurableEmbedding,
    pairToPlane_measurableEmbedding.injective.preimage_image]

theorem pairToPlane_integral (S : Set (ℝ × ℝ)) (f : EuclideanSpace ℝ (Fin 2) → ℝ) :
    (∫ x in pairToPlane '' S, f x) = ∫ p in S, f (pairToPlane p) :=
  pairToPlane_measurePreserving.setIntegral_image_emb pairToPlane_measurableEmbedding f S

theorem euclideanRadialSector_volume {l r : ℝ} {R : ℝ → ℝ}
    (hlr : l ≤ r) (hRcont : ContinuousOn R (Icc l r))
    (hR : ∀ q ∈ Icc l r, 0 ≤ R q) :
    volume (euclideanRadialSector l r R) =
      ENNReal.ofReal (∫ q in l..r, (R q) ^ 2 / 2) := by
  rw [euclideanRadialSector, pairToPlane_volume, radialSector_volume hlr hRcont hR]

theorem euclideanRadialSector_area {l r : ℝ} {R : ℝ → ℝ}
    (hlr : l ≤ r) (hRcont : ContinuousOn R (Icc l r))
    (hR : ∀ q ∈ Icc l r, 0 ≤ R q) :
    volume.real (euclideanRadialSector l r R) =
      ∫ q in l..r, (R q) ^ 2 / 2 := by
  rw [Measure.real, euclideanRadialSector_volume hlr hRcont hR, ENNReal.toReal_ofReal]
  exact intervalIntegral.integral_nonneg_of_forall hlr (fun _ => by positivity)

theorem isCompact_euclideanRadialSector {l r : ℝ} {R : ℝ → ℝ}
    (hRcont : ContinuousOn R (Icc l r)) (hR : ∀ q ∈ Icc l r, 0 ≤ R q) :
    IsCompact (euclideanRadialSector l r R) :=
  (isCompact_radialSector hRcont hR).image continuous_pairToPlane

theorem mem_euclideanRadialSector {l r : ℝ} {R : ℝ → ℝ}
    {b : EuclideanSpace ℝ (Fin 2)} :
    b ∈ euclideanRadialSector l r R ↔
      ∃ q ∈ Icc l r, ∃ s ∈ Icc 0 (R q), b = !₂[q * s, s] := by
  constructor
  · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x.1, hx.1, x.2, hx.2, rfl⟩
  · rintro ⟨q, hq, s, hs, rfl⟩
    exact ⟨radialMap (q, s), ⟨(q, s), ⟨hq, hs⟩, rfl⟩, rfl⟩

theorem isCompact_euclideanRadialBand {l r ρ : ℝ} {R : ℝ → ℝ}
    (hRcont : ContinuousOn R (Icc l r)) (hR : ∀ q ∈ Icc l r, ρ ≤ R q) :
    IsCompact (euclideanRadialBand l r ρ R) :=
  (isCompact_radialBand hRcont hR).image continuous_pairToPlane

theorem mem_euclideanRadialBand {l r ρ : ℝ} {R : ℝ → ℝ}
    {b : EuclideanSpace ℝ (Fin 2)} :
    b ∈ euclideanRadialBand l r ρ R ↔
      ∃ q ∈ Icc l r, ∃ s ∈ Icc ρ (R q), b = !₂[q * s, s] := by
  constructor
  · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x.1, hx.1, x.2, hx.2, rfl⟩
  · rintro ⟨q, hq, s, hs, rfl⟩
    exact ⟨radialMap (q, s), ⟨(q, s), ⟨hq, hs⟩, rfl⟩, rfl⟩

theorem euclideanRadialBand_height_pos {l r ρ : ℝ} {R : ℝ → ℝ}
    (hρ : 0 < ρ) {b : EuclideanSpace ℝ (Fin 2)}
    (hb : b ∈ euclideanRadialBand l r ρ R) : 0 < b 1 := by
  rcases mem_euclideanRadialBand.mp hb with ⟨q, _, s, hs, rfl⟩
  exact lt_of_lt_of_le hρ hs.1

theorem euclideanRadialBand_weighted_integral {l r ρ : ℝ} {R F : ℝ → ℝ}
    (hlr : l ≤ r) (hρ : 0 < ρ) (hRcont : ContinuousOn R (Icc l r))
    (hR : ∀ q ∈ Icc l r, ρ ≤ R q) (hFcont : ContinuousOn F (Icc l r)) :
    (∫ b in euclideanRadialBand l r ρ R, F (b 0 / b 1)) =
      ∫ q in l..r, ((R q) ^ 2 - ρ ^ 2) / 2 * F q := by
  rw [euclideanRadialBand, pairToPlane_integral]
  exact radialBand_weighted_integral hlr hρ hRcont hR hFcont

theorem euclideanRadialBand_weighted_le_full {l r ρ : ℝ} {R F : ℝ → ℝ}
    (hlr : l ≤ r) (hρ : 0 < ρ) (hRcont : ContinuousOn R (Icc l r))
    (hR : ∀ q ∈ Icc l r, ρ ≤ R q) (hFcont : ContinuousOn F (Icc l r))
    (hF : ∀ q ∈ Icc l r, 0 ≤ F q) :
    (∫ b in euclideanRadialBand l r ρ R, F (b 0 / b 1)) ≤
      ∫ q in l..r, (R q) ^ 2 / 2 * F q := by
  rw [euclideanRadialBand, pairToPlane_integral]
  exact radialBand_weighted_le_full hlr hρ hRcont hR hFcont hF

end AngularCaps

end

end OAI
