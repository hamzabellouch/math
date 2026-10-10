import OAI.MeasureTheory.Falconer.Radial.RadialTestEnergy

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem radialEnergyMajorant_lt_top (α β : Measure Plane) {D s t p : ℝ}
    (hp : 0 < p) (hp2 : p < 2) (ht : 0 < t) (htp : t < 2-p)
    (hα : rieszEnergy α s < ∞) (hβ : rieszEnergy β t < ∞) :
    radialEnergyMajorant α β D s t p < ∞ := by
  unfold radialEnergyMajorant
  apply ENNReal.mul_lt_top
  · exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  · apply ENNReal.mul_lt_top
    · exact ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by linarith)
          (angularEnergyConstant_lt_top (div_pos ht (sub_pos.mpr hp2))
            ((div_lt_one (sub_pos.mpr hp2)).mpr htp)).ne)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hβ.ne)
    · exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
        (ENNReal.mul_lt_top (by norm_num) hα).ne

theorem finite_radial_testNorm_integral (α β : Measure Plane)
    [IsFiniteMeasure α] [IsFiniteMeasure β] {K : Set Plane} (hK : IsCompact K)
    (hαK : ∀ᵐ z ∂α, z ∈ K) {D s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hs1 : 1 < s) (hs2 : s < 2)
    (hD : 0 < D) (hupt : (2-s)*p < t) (htp : t < 2-p)
    (hdiam : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D)
    (hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D)
    (hx : ∀ᵐ x ∂β, ∀ᵐ y ∂α, y ≠ x)
    (hα : rieszEnergy α s < ∞) (hβ : rieszEnergy β t < ∞) :
    (∫⁻ x, (sourceTestNorm q (α.map (sourceRadialUnit x)))^p ∂β) < ∞ := by
  have hb := radial_testNorm_energy_bound α β hK hαK hpq hp2 hs1 hs2 hD hupt htp
    hdiam hbound hx
  have ht : 0 < t := (mul_pos (by linarith : 0 < 2-s) hpq.pos).trans hupt
  have hR := radialEnergyMajorant_lt_top α β (D := D) hpq.pos hp2 ht htp hα hβ
  by_contra h
  have he : (∫⁻ x, (sourceTestNorm q (α.map (sourceRadialUnit x)))^p ∂β) = ∞ :=
    top_unique (not_lt.mp h)
  rw [he,ENNReal.mul_top (radialEnergyPrefactor_pos hs1 hs2).ne'] at hb
  exact (not_le_of_gt hR) hb

end PlanarFalconer

end OAI
