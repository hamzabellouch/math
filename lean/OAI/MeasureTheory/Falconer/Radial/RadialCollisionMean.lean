import OAI.MeasureTheory.Falconer.Radial.RadialCollisionMass
import OAI.MeasureTheory.Falconer.Radial.ReverseRadialTruncation
import OAI.MeasureTheory.Falconer.Recursion.CriticalTruncatedPotential

namespace OAI

/-! # Original-pin radial collision means on a profile interval

The comparison source is the full conditional source law. The reverse pin
law remains a restriction of the original pin measure; no fiber is normalized.
-/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radial_collision_mean_bound (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (z : Space d) {D Kν Kμ q : ℝ} (hD : 1 ≤ D) (hKν : 1 ≤ Kν) (hq : 0 ≤ q)
    (hmass : ν univ ≤ 1) (g k : ℕ)
    (hdiag : ∀ x, (z,x) ∈ G → x ≠ z)
    (hsource : ∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧
      ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D)
    (hball : ∀ j : ℕ, j ≤ g+k →
      μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (Kμ*(1/(2:ℝ)^j)^q))
    (hcap : ∀ r : ℝ, 1/(2:ℝ)^(g+k) ≤ r → ∀ u : Space d, ‖u‖ = 1 →
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (Kν*r^q)) :
    (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ (1/(2:ℝ)^(g+k)) (z,x) ∂ν) ≤
      ENNReal.ofReal (2*Kν*(3*D)^q*(1/(2:ℝ)^(g+k))^q)*
        (ENNReal.ofReal ((2:ℝ)^q)*
          (ENNReal.ofReal Kμ+(k:ℝ≥0∞)*ENNReal.ofReal (Kμ*(2:ℝ)^q))) := by
  let δ : ℝ := 1/(2:ℝ)^(g+k)
  let L : ℝ := 2*Kν*(3*D)^q
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hK0 : 0 < Kν := lt_of_lt_of_le zero_lt_one hKν
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hS : μ.restrict {y | ‖y-z‖ < 1/(2:ℝ)^g} = μ :=
    Measure.restrict_eq_self_of_ae_mem (hsource.mono fun _ h => h.1)
  have hp : ∀ᵐ y ∂μ,
      ν {x | (z,x) ∈ G ∧ dist (normalize (y-x)) (normalize (z-x)) ≤ δ} ≤
        ENNReal.ofReal (L*δ^q)*ENNReal.ofReal ((1/max ‖y-z‖ δ)^q) := by
    filter_upwards [hsource] with y hy
    have hy1 : ‖y-z‖ ≤ 1 := hy.1.le.trans (by
      apply (div_le_one (by positivity)).mpr
      exact one_le_pow₀ (by norm_num))
    have hh := reverse_radial_collision_truncated ν G z y hdiag hD hδ hKν hq hmass hy1 hy.2 hcap
    apply hh.trans_eq
    change ENNReal.ofReal (L*(δ/max ‖y-z‖ δ)^q) = _
    rw [show δ/max ‖y-z‖ δ = δ*(1/max ‖y-z‖ δ) by ring,
      Real.mul_rpow hδ.le (by positivity)]
    rw [← ENNReal.ofReal_mul (mul_nonneg hL (Real.rpow_nonneg hδ.le _))]
    congr 1
    ring
  rw [radial_collision_original_pin_fubini μ ν G hG z]
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (L*δ^q)*ENNReal.ofReal ((1/max ‖y-z‖ δ)^q) ∂μ :=
      lintegral_mono_ae hp
    _ = ENNReal.ofReal (L*δ^q)*(∫⁻ y in {y | ‖y-z‖ < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/max ‖y-z‖ δ)^q) ∂μ) := by
      rw [hS,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := mul_le_mul' le_rfl
      (truncated_scalar_potential_critical μ (fun y => ‖y-z‖) (by fun_prop)
        (fun _ => norm_nonneg _) hq g k hball)

end Falconer

end OAI
