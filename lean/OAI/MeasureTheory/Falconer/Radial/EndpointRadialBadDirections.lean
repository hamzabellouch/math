import OAI.MeasureTheory.Falconer.Angular.EndpointBadDirections
import OAI.MeasureTheory.Falconer.Radial.RadialBadWitness
import OAI.MeasureTheory.Falconer.Radial.RadialSphereBounds

namespace OAI

/-! # The endpoint envelope deletes only power-small original witness pairs -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem endpoint_radial_bad_directions (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C : ℝ} (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
    (hζ : 0 < ζ) (hC : 0 ≤ C) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+3)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (w₀ : Sphere (h+3)) (G : Set (Space (h+3) × Space (h+3))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ, ‖z‖ ≤ 1/4) →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ,
        (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N →
          ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+3)) < 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) ∧
        (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ν {x | (z,x) ∈ G ∧ |inner ℝ (w:Space (h+3)) (normalize (x-z))| ≤ r} ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ))) →
      ∃ B : Set (Sphere (h+3)), MeasurableSet B ∧
        {w : Sphere (h+3) | ∃ S : Finset (Space (h+3)),
          (S.card:ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-b) ∧
          ENNReal.ofReal ((1/(2:ℝ)^N)^b) ≤
            μ {z | ∃ v ∈ S, ‖perpendicularPart (w:Space (h+3)) (z-v)‖ ≤ C*(1/(2:ℝ)^N)}} ⊆ B ∧
        (μ.prod ν) (radialBadWitness w₀ G B) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
  obtain ⟨ε,b,hε,hb,N₀,hN₀⟩ := endpoint_bad_direction_envelope hLW ht ht' hζ hC
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ ν _ _ hν w₀ G hG hdiag hμ hμball hdata
  obtain ⟨B,hB,hcontains,hbound⟩ := hN₀ N hN μ hμ hμball
  refine ⟨B,hB,hcontains,?_⟩
  have hsmall : ∀ᵐ z ∂μ, originalRadialSphereLaw w₀ ν G z B ≤
      ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
    filter_upwards [hdata] with z hz
    apply hbound (originalRadialSphereLaw w₀ ν G z)
      ((originalRadialSphereLaw_mass_le w₀ ν G z).trans hν)
    · intro w j hj
      rw [originalRadialSphereLaw_ball w₀ ν G z (hdiag z)]
      exact hz.1 w j hj
    · intro w r hr hr1
      rw [originalRadialSphereLaw_slab w₀ ν G z (hdiag z)]
      exact hz.2 w r hr hr1
  simpa only [measure_univ,mul_one] using radial_bad_witness_mass w₀ μ ν G hG B hB _ hsmall

end Falconer

end OAI
