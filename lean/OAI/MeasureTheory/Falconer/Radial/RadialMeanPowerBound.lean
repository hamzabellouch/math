import OAI.MeasureTheory.Falconer.Radial.RadialMeanPowers

namespace OAI

/-! # Uniform power form of the original-pin radial mean bound -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem ennreal_radial_mean_coefficient {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (k : ℕ) :
    ENNReal.ofReal a*(ENNReal.ofReal c*
      (ENNReal.ofReal b+(k:ℝ≥0∞)*ENNReal.ofReal (b*c))) =
        ENNReal.ofReal (a*c*(b+(k:ℝ)*(b*c))) := by
  have he : ENNReal.ofReal b+(k:ℝ≥0∞)*ENNReal.ofReal (b*c) =
      ENNReal.ofReal (b+(k:ℝ)*(b*c)) := by
    rw [ENNReal.ofReal_add hb (by positivity),
      ENNReal.ofReal_mul (Nat.cast_nonneg k),ENNReal.ofReal_natCast]
  rw [he,← ENNReal.ofReal_mul hc,← ENNReal.ofReal_mul ha]
  congr 1
  ring

theorem radial_cap_extend_large (ν : Measure (Space d)) (G : Set (Space d × Space d))
    (z : Space d) {δ K q : ℝ} (hK : 1 ≤ K) (hq : 0 ≤ q) (hmass : ν univ ≤ 1)
    (hcap : ∀ r : ℝ, δ ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K*r^q)) :
    ∀ r : ℝ, δ ≤ r → ∀ u : Space d, ‖u‖ = 1 →
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K*r^q) := by
  intro r hr u hu
  by_cases hr1 : r ≤ 1
  · exact hcap r hr hr1 u hu
  · have hr1' : 1 ≤ r := (lt_of_not_ge hr1).le
    have hp : 1 ≤ r^q := Real.one_le_rpow hr1' hq
    have hb : 1 ≤ K*r^q := by nlinarith
    exact ((measure_mono (subset_univ _)).trans hmass).trans
      (by simpa using ENNReal.ofReal_le_ofReal hb)

theorem eventually_radial_collision_mean {D η q : ℝ}
    (hD : 1 ≤ D) (hη : 0 < η) (hq : 0 ≤ q) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g k : ℕ, k ≤ N →
      ∀ (μ ν : Measure (Space d)) [SFinite μ] [SFinite ν],
      ∀ (G : Set (Space d × Space d)), MeasurableSet G → ∀ z : Space d,
      ν univ ≤ 1 → (∀ x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) →
      (∀ j : ℕ, j ≤ g+k → μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((((2:ℝ)^N)^η*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) →
      (∀ r : ℝ, 1/(2:ℝ)^(g+k) ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^η*r^q)) →
      (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ (1/(2:ℝ)^(g+k)) (z,x) ∂ν) ≤
        ENNReal.ofReal (((2:ℝ)^N)^(3*η)*((2:ℝ)^k)^(-q)) := by
  obtain ⟨N₀,hN₀⟩ := eventually_radial_mean_coefficient hD hη
  refine ⟨N₀,?_⟩
  intro N hN g k hk μ ν _ _ G hG z hmass hdiag hsource hball hcap
  have hK : 1 ≤ ((2:ℝ)^N)^η := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hη.le
  have hb := radial_collision_mean_bound μ ν G hG z hD hK hq hmass g k hdiag hsource hball
    (radial_cap_extend_large ν G z hK hq hmass hcap)
  apply hb.trans
  rw [ennreal_radial_mean_coefficient (by positivity) (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (hN₀ N hN g k hk)

end Falconer

end OAI
