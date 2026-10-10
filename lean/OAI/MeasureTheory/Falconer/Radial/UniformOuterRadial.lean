import OAI.MeasureTheory.Falconer.Radial.OuterRadialPruning

namespace OAI

/-! # A common outer-radial cutoff for all contact exponents above a fixed positive floor -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem eventually_radial_mean_coefficient_uniform {D η₀ q : ℝ} (hD : 1 ≤ D) (hη₀ : 0 < η₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η → ∀ g k : ℕ, k ≤ N →
      (2*((2:ℝ)^N)^η*(3*D)^q*(1/(2:ℝ)^(g+k))^q)*
        (2:ℝ)^q*(((2:ℝ)^N)^η*((2:ℝ)^g)^q+
          (k:ℝ)*(((2:ℝ)^N)^η*((2:ℝ)^g)^q*(2:ℝ)^q)) ≤
      ((2:ℝ)^N)^(3*η)*((2:ℝ)^k)^(-q) := by
  let B := 2*(3*D)^q*(2:ℝ)^q
  let C := B*(1+(2:ℝ)^q)
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨N₀,hN₀⟩ := PlanarFalconer.fixed_linear_subpower C hC hη₀
  refine ⟨N₀,fun N hN η hηge g k hk => ?_⟩
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hcoef : B*(1+(k:ℝ)*(2:ℝ)^q) ≤ R^η := by
    apply le_trans ?_ ((hN₀ N hN).trans (Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ (by norm_num)) hηge))
    have hkn : (k:ℝ) ≤ N := by exact_mod_cast hk
    have hp : 0 ≤ (2:ℝ)^q := by positivity
    have hnum : 1+(k:ℝ)*(2:ℝ)^q ≤ (1+(2:ℝ)^q)*(1+2*(N:ℝ)) := by
      nlinarith [show (0:ℝ) ≤ N from Nat.cast_nonneg N]
    exact (mul_le_mul_of_nonneg_left hnum hB).trans_eq (by dsimp [C]; ring)
  calc
    _ = (B*(1+(k:ℝ)*(2:ℝ)^q))*(R^η*R^η)*
        (((2:ℝ)^g)^q*(1/(2:ℝ)^(g+k))^q) := by dsimp [B,R]; ring
    _ = (B*(1+(k:ℝ)*(2:ℝ)^q))*R^(2*η)*((2:ℝ)^k)^(-q) := by
      rw [dyadic_radial_power_cancel,← Real.rpow_add hR,show η+η = 2*η by ring]
    _ ≤ R^η*R^(2*η)*((2:ℝ)^k)^(-q) := by gcongr
    _ = _ := by
      rw [← Real.rpow_add hR,show η+2*η = 3*η by ring]

theorem eventually_radial_collision_mean_uniform {D η₀ q : ℝ}
    (hD : 1 ≤ D) (hη₀ : 0 < η₀) (hq : 0 ≤ q) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η → ∀ g k : ℕ, k ≤ N →
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
  obtain ⟨N₀,hN₀⟩ := eventually_radial_mean_coefficient_uniform hD hη₀
  refine ⟨N₀,?_⟩
  intro N hN η hηge g k hk μ ν _ _ G hG z hmass hdiag hsource hball hcap
  have hK : 1 ≤ ((2:ℝ)^N)^η := Real.one_le_rpow (one_le_pow₀ (by norm_num)) (hη₀.trans_le hηge).le
  have hb := radial_collision_mean_bound μ ν G hG z hD hK hq hmass g k hdiag hsource hball
    (radial_cap_extend_large ν G z hK hq hmass hcap)
  apply hb.trans
  rw [ennreal_radial_mean_coefficient (by positivity) (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (hN₀ N hN η hηge g k hk)

theorem outer_radial_interval_pruning_uniform {D η₀ q : ℝ}
    (hD : 1 ≤ D) (hη₀ : 0 < η₀) (hq : 0 ≤ q) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η → ∀ g k : ℕ, k ≤ N →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ,
        (∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) ∧
        (∀ j : ℕ, j ≤ g+k → μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((((2:ℝ)^N)^η*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) ∧
        (∀ r : ℝ, 1/(2:ℝ)^(g+k) ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
          ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^η*r^q))) →
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
        (μ.prod ν) (G \ H) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-η)) ∧
        ∀ p ∈ H, radialCollisionMass μ (1/(2:ℝ)^(g+k)) p ≤
          ENNReal.ofReal (((2:ℝ)^N)^(4*η)*((2:ℝ)^k)^(-q)) := by
  obtain ⟨N₀,hN₀⟩ := eventually_radial_collision_mean_uniform (d := d) hD hη₀ hq
  refine ⟨N₀,?_⟩
  intro N hN η hηge g k hk μ ν _ _ G hG hdiag hdata
  let R : ℝ := (2:ℝ)^N
  let S : ℝ := ((2:ℝ)^k)^(-q)
  have hR : 0 < R := by dsimp [R]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hF : 0 < R^(4*η)*S := by positivity
  have hmean : ∀ᵐ z ∂μ,
      (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ (1/(2:ℝ)^(g+k)) (z,x) ∂ν) ≤
        ENNReal.ofReal (R^(3*η)*S) := by
    filter_upwards [hdata] with z hz
    exact hN₀ N hN η hηge g k hk μ ν G hG z (by simp) (hdiag z) hz.1 hz.2.1 hz.2.2
  obtain ⟨H,hH,hHG,hcost,hcap⟩ := radial_collision_pruning μ ν G hG
    (1/(2:ℝ)^(g+k)) (ENNReal.ofReal_pos.mpr hF).ne' ENNReal.ofReal_ne_top hmean
  refine ⟨H,hH,hHG,hcost.trans_eq ?_,hcap⟩
  rw [measure_univ,mul_one,← ENNReal.ofReal_div_of_pos hF]
  congr 1
  calc
    (R^(3*η)*S)/(R^(4*η)*S) = R^(3*η)/R^(4*η) := by
      exact mul_div_mul_right _ _ (ne_of_gt hS)
    _ = R^(3*η-4*η) := (Real.rpow_sub hR _ _).symm
    _ = R^(-η) := by congr 1; ring

end Falconer

end OAI
