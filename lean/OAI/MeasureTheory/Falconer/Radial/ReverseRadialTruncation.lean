import OAI.MeasureTheory.Falconer.Radial.ReverseRadialMass

namespace OAI

/-! # A truncated-kernel bound for the mass of original collision pins -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem reverse_radial_collision_truncated (ν : Measure (Space n))
    (G : Set (Space n × Space n)) (z y : Space n)
    (hdiag : ∀ x, (z,x) ∈ G → x ≠ z) {D δ K q : ℝ}
    (hD : 1 ≤ D) (hδ : 0 < δ) (hK : 1 ≤ K) (hq : 0 ≤ q)
    (hmass : ν univ ≤ 1) (hyz : ‖y-z‖ ≤ 1)
    (hbound : ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D)
    (hcap : ∀ r : ℝ, δ ≤ r → ∀ u : Space n, ‖u‖ = 1 →
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
        ENNReal.ofReal (K*r^q)) :
    ν {x | (z,x) ∈ G ∧ dist (normalize (y-x)) (normalize (z-x)) ≤ δ} ≤
      ENNReal.ofReal ((2*K*(3*D)^q)*(δ/max ‖y-z‖ δ)^q) := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  by_cases hnear : ‖y-z‖ ≤ δ
  · rw [max_eq_right hnear,div_self hδ.ne',Real.one_rpow,mul_one]
    have hp : 1 ≤ (3*D)^q := Real.one_le_rpow (by linarith) hq
    have hL : 1 ≤ 2*K*(3*D)^q := by nlinarith
    exact ((measure_mono (subset_univ _)).trans hmass).trans
      (by simpa using ENNReal.ofReal_le_ofReal hL)
  · have hr : δ < ‖y-z‖ := lt_of_not_ge hnear
    have hr0 : 0 < ‖y-z‖ := hδ.trans hr
    have hy : y ≠ z := sub_ne_zero.mp (norm_pos_iff.mp hr0)
    have hrange : δ ≤ 3*(D*δ/‖y-z‖) := by
      rw [show 3*(D*δ/‖y-z‖) = 3*D*δ/‖y-z‖ by ring]
      apply (le_div_iff₀ hr0).mpr
      nlinarith
    have hh := reverse_radial_collision_mass ν G z y hy hdiag hD0 hδ hbound
      (fun u hu => hcap (3*(D*δ/‖y-z‖)) hrange u hu)
    apply hh.trans_eq
    rw [max_eq_left hr.le]
    rw [show 3*(D*δ/‖y-z‖) = (3*D)*(δ/‖y-z‖) by ring,
      Real.mul_rpow (by positivity) (by positivity)]
    conv_lhs =>
      lhs
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num]
    rw [← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring

end Falconer

end OAI
