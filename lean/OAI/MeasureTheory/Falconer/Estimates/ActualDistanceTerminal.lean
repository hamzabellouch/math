import OAI.MeasureTheory.Falconer.Shells.HighShellProfileMass

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem coincidence_trivial_profile_bound (d : PositiveDistanceData) {B : ℕ} {δ : ℝ}
    (hd : RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass)
    (ha : d.a ≤ d.N) (hX : d.X.length = d.a) (hY : d.Y.length = d.a) :
    d.coincidence.toReal ≤ (2:ℝ)^((d.t:ℝ)-d.a)*((2:ℝ)^d.N)^(12*d.lam) := by
  let := hd.probability
  have hmass := d.normalized_cellPair_profile_mass hd ha hX hY
  have hquad : (d.cellPair.prod d.cellPair) univ = d.cellPair univ*d.cellPair univ := by
    rw [← univ_prod_univ,Measure.prod_prod]
  have hc : d.coincidence.toReal ≤ d.normalization.toReal*(d.cellPair.real univ)^2 := by
    rw [d.coincidence_four_point,ENNReal.toReal_mul]
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    calc
      _ ≤ ((d.cellPair.prod d.cellPair) univ).toReal :=
        ENNReal.toReal_mono (measure_ne_top (d.cellPair.prod d.cellPair) univ)
          (measure_mono (subset_univ _))
      _ = _ := by rw [hquad,ENNReal.toReal_mul]; simp only [pow_two,measureReal_def]
  have he : d.normalization.toReal*(d.cellPair.real univ)^2 =
      (2:ℝ)^((d.t:ℝ)-d.a)*(d.levelMass^(-2:ℤ)*d.cellPair.real univ)^2 := by
    rw [normalization,ENNReal.toReal_ofReal (by positivity)]
    simp only [zpow_neg,zpow_ofNat]
    field_simp
  have hp := pow_le_pow_left₀ (show 0 ≤ d.levelMass^(-2:ℤ)*d.cellPair.real univ by positivity) hmass 2
  have hr : (((2:ℝ)^d.N)^(6*d.lam))^2 = ((2:ℝ)^d.N)^(12*d.lam) := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ (2:ℝ)^d.N)]
    congr 1
    norm_num
    ring
  rw [hr] at hp
  exact hc.trans (he.trans_le (mul_le_mul_of_nonneg_left hp (by positivity)))

theorem actual_distance_terminal (d : PositiveDistanceData) {B : ℕ} {δ : ℝ}
    (hd : RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass)
    (ha : d.a ≤ d.N) (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (ht : d.t ≤ d.a+100*d.q) :
    d.coincidence.toReal ≤ (2:ℝ)^(200*(d.q:ℝ))*((2:ℝ)^d.N)^(12*d.lam) := by
  have htR : (d.t:ℝ) ≤ (d.a:ℝ)+100*d.q := by exact_mod_cast ht
  have he : (2:ℝ)^((d.t:ℝ)-d.a) ≤ (2:ℝ)^(200*(d.q:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [show (0:ℝ) ≤ d.q by positivity])
  exact (d.coincidence_trivial_profile_bound hd ha hX hY).trans
    (mul_le_mul_of_nonneg_right he (by positivity))

end PositiveDistanceData

end PlanarFalconer

end OAI
