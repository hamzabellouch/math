import OAI.MeasureTheory.Falconer.Radial.RadialFatou
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable def radialEnergyPrefactor (s p : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (sourceEnergyConstant 2 s))^(p/2) *
    (ENNReal.ofReal (sourceEnergyConstant 1 (2-s)))^(p/2)

noncomputable def radialEnergyMajorant (α β : Measure Plane) (D s t p : ℝ) : ℝ≥0∞ :=
  ((ENNReal.ofReal (D+1))^p * (ENNReal.ofReal ((D+1)^(t-(2-s)*p)))^(1/2 : ℝ)) *
    ((angularEnergyConstant (t/(2-p)))^((2-p)/2) *
      (rieszEnergy β t)^(1/2 : ℝ) * (2*rieszEnergy α s)^(p/2))

theorem radialEnergyPrefactor_pos {s p : ℝ} (hs1 : 1 < s) (hs2 : s < 2) :
    0 < radialEnergyPrefactor s p := by
  have h₁ := sourceEnergyConstant_pos (by linarith : 0 < 2-s) (by linarith : 2-s < 1)
  have h₂ := sourceEnergyConstant_pos (by linarith : 0 < s) hs2
  unfold radialEnergyPrefactor
  exact pos_iff_ne_zero.mpr (mul_ne_zero
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr h₂) ENNReal.ofReal_ne_top).ne'
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr h₁) ENNReal.ofReal_ne_top).ne')

theorem radialEnergyPrefactor_ne_top {s p : ℝ} (hp : 0 ≤ p) :
    radialEnergyPrefactor s p ≠ ∞ := by
  apply ENNReal.mul_ne_top
  · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top

theorem radial_testNorm_energy_bound (α β : Measure Plane)
    [IsFiniteMeasure α] [IsFiniteMeasure β] {K : Set Plane} (hK : IsCompact K)
    (hα : ∀ᵐ z ∂α, z ∈ K) {D s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hs1 : 1 < s) (hs2 : s < 2)
    (hD : 0 < D) (hupt : (2-s)*p < t) (htp : t < 2-p)
    (hdiam : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D)
    (hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D)
    (hx : ∀ᵐ x ∂β, ∀ᵐ y ∂α, y ≠ x) :
    radialEnergyPrefactor s p *
      (∫⁻ x, (sourceTestNorm q (α.map (sourceRadialUnit x)))^p ∂β) ≤
        radialEnergyMajorant α β D s t p := by
  let ε := fun n : ℕ => 1/((n : ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε1 (n : ℕ) : ε n ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let J := fun n => ∫⁻ x, (∫⁻ θ in Ioc 0 (2*Real.pi),
    (sourceRadialDensity (fun y => ENNReal.ofReal
      (sourceSmoothDensity α (sourceMollifier (ε n) (hε n)) y)) x θ)^p) ∂β
  let c := radialEnergyPrefactor s p
  let R := radialEnergyMajorant α β D s t p
  have hc0 : c ≠ 0 := (radialEnergyPrefactor_pos hs1 hs2).ne'
  have hct : c ≠ ∞ := radialEnergyPrefactor_ne_top hpq.nonneg
  have hJ (n : ℕ) : c * J n ≤ R :=
    mollified_radial_density_energy_bound α β hK hα hpq hp2 hs1 hs2 hD hupt htp
      hdiam hbound (ε n) (hε n) (hε1 n)
  have hJ' (n : ℕ) : J n ≤ c⁻¹ * R := by
    calc
      J n = c⁻¹*(c*J n) := by rw [← mul_assoc,ENNReal.inv_mul_cancel hc0 hct,one_mul]
      _ ≤ _ := mul_le_mul_right (hJ n) _
  have hl : liminf J atTop ≤ c⁻¹*R := by
    have h := liminf_le_liminf (f := atTop) (Eventually.of_forall hJ')
    simpa only [liminf_const] using h
  have hf := radial_testNorm_fatou α β hε hlim hpq hx
  calc
    _ ≤ c*(c⁻¹*R) := mul_le_mul_right (hf.trans hl) c
    _ = R := by rw [← mul_assoc,ENNReal.mul_inv_cancel hc0 hct,one_mul]

end PlanarFalconer

end OAI
