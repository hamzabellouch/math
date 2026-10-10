import OAI.MeasureTheory.Falconer.Radial.UniformOuterRadial
import OAI.MeasureTheory.Falconer.Radial.RadialCollisionWidths

namespace OAI

/-! # Outer-interval pruning with the fixed widths used by the cell multiplication lemma -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem dyadic_shifted_decay {g v J : ℕ} (h : g+J ≤ v) (q : ℝ) :
    ((2:ℝ)^((v-J)-g))^(-q) = ((2:ℝ)^J)^q*((2:ℝ)^(v-g))^(-q) := by
  have he : v-g = J+((v-J)-g) := by omega
  conv_rhs => rw [he,pow_add]
  rw [Real.mul_rpow (by positivity) (by positivity),Real.rpow_neg (by positivity)]
  rw [← mul_assoc,← Real.rpow_add (by positivity),add_neg_cancel,Real.rpow_zero,one_mul]

theorem outer_radial_interval_fixed_width {D η₀ q : ℝ}
    (hD : 1 ≤ D) (hη₀ : 0 < η₀) (hq : 0 ≤ q) (C : ℝ) :
    ∃ J N₀ : ℕ, ∀ N ≥ N₀, ∀ η : ℝ, η₀ ≤ η →
      ∀ g v : ℕ, g+J ≤ v → v ≤ N →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ,
        (∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) ∧
        (∀ j : ℕ, j ≤ v → μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((((2:ℝ)^N)^η*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) ∧
        (∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
          ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^η*r^q))) →
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
        (μ.prod ν) (G \ H) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-η)) ∧
        ∀ p ∈ H, radialCollisionMass μ (C/(2:ℝ)^v) p ≤
          ENNReal.ofReal (((2:ℝ)^N)^(5*η)*((2:ℝ)^(v-g))^(-q)) := by
  obtain ⟨J,hJ⟩ := dyadic_width_rounding C
  obtain ⟨N₁,hN₁⟩ := outer_radial_interval_pruning_uniform (d := d) hD hη₀ hq
  obtain ⟨N₂,hN₂⟩ := Regularization.fixed_constant_absorbed hη₀ (((2:ℝ)^J)^q)
  refine ⟨J,max N₁ N₂,?_⟩
  intro N hN η hη g v hgv hvN μ ν _ _ G hG hdiag hdata
  have hJv : J ≤ v := by omega
  have hg : g ≤ v-J := by omega
  have he : g+((v-J)-g) = v-J := Nat.add_sub_of_le hg
  have hr : 1/(2:ℝ)^v ≤ 1/(2:ℝ)^(v-J) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hdata' : ∀ᵐ z ∂μ,
      (∀ᵐ y ∂μ, ‖y-z‖ < 1/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D) ∧
      (∀ j : ℕ, j ≤ g+((v-J)-g) → μ {y | ‖y-z‖ < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((((2:ℝ)^N)^η*((2:ℝ)^g)^q)*(1/(2:ℝ)^j)^q)) ∧
      (∀ r : ℝ, 1/(2:ℝ)^(g+((v-J)-g)) ≤ r → r ≤ 1 → ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^η*r^q)) := by
    filter_upwards [hdata] with z hz
    refine ⟨hz.1,fun j hj => hz.2.1 j (by omega),?_⟩
    intro r hrr hr1 u hu
    rw [he] at hrr
    exact hz.2.2 r (hr.trans hrr) hr1 u hu
  obtain ⟨H,hH,hHG,hdel,hbound⟩ := hN₁ N ((le_max_left _ _).trans hN) η hη g
    ((v-J)-g) (by omega) μ ν G hG hdiag hdata'
  refine ⟨H,hH,hHG,hdel,fun p hp => ?_⟩
  apply (radialCollisionMass_mono μ p (hJ v hJv)).trans
  rw [← he]
  apply (hbound p hp).trans
  apply ENNReal.ofReal_le_ofReal
  rw [dyadic_shifted_decay hgv]
  have hconst : ((2:ℝ)^J)^q ≤ ((2:ℝ)^N)^η :=
    (hN₂ N ((le_max_right _ _).trans hN)).trans
      (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hη)
  calc
    _ = (((2:ℝ)^N)^(4*η)*((2:ℝ)^J)^q)*((2:ℝ)^(v-g))^(-q) := by ring
    _ ≤ (((2:ℝ)^N)^(4*η)*((2:ℝ)^N)^η)*((2:ℝ)^(v-g))^(-q) := by gcongr
    _ = _ := by rw [← Real.rpow_add (by positivity),show 4*η+η = 5*η by ring]

end Falconer

end OAI
