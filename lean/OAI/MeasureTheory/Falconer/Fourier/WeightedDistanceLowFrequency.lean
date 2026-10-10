import OAI.MeasureTheory.Falconer.Estimates.ActualDistanceEquation20
import OAI.MeasureTheory.Falconer.Estimates.ProfileMassError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem weightedDistance_mass_le (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) :
    d.weightedDistance.real univ ≤
      ((d.ρ (d.Q.descendant d.X).carrier).toReal / d.levelMass) *
      ((d.ρ (d.Q.descendant d.Y).carrier).toReal / d.levelMass) := by
  have hm := Measure.le_iff.mp (d.weightedPair_le hQ hs) univ MeasurableSet.univ
  have h := ENNReal.toReal_mono (by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hm
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at h
  have hp : d.cellPair univ =
      d.ρ (d.Q.descendant d.X).carrier * d.ρ (d.Q.descendant d.Y).carrier := by
    unfold cellPair
    rw [← univ_prod_univ,Measure.prod_prod,Measure.restrict_apply_univ,Measure.restrict_apply_univ]
  rw [hp,ENNReal.toReal_mul] at h
  have hw : d.weightedDistance.real univ = (d.weightedPair univ).toReal := by
    rw [measureReal_def,weightedDistance,Measure.map_apply (by fun_prop) MeasurableSet.univ,preimage_univ]
  rw [hw]
  convert h using 1
  norm_num only [zpow_neg,zpow_ofNat]
  field_simp

theorem weightedDistance_profile_mass (d : PositiveDistanceData) {B : ℕ} {δ : ℝ}
    (hd : RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass)
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (ha : d.a ≤ d.N)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a) :
    d.weightedDistance.real univ ≤ ((2:ℝ)^d.N)^(6*d.lam) := by
  let := hd.probability
  have hx := hd.normalized_cell_mass_le ha hX
  have hy := hd.normalized_cell_mass_le ha hY
  have h := mul_le_mul hx hy (by positivity) (by positivity)
  rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^d.N),
    show 3*d.lam+3*d.lam = 6*d.lam by ring] at h
  exact (d.weightedDistance_mass_le hQ hs).trans h

theorem weightedDistance_low_frequency (d : PositiveDistanceData) {B : ℕ} {δ : ℝ}
    (hd : RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass)
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (ha : d.a ≤ d.N)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a) :
    (2:ℝ)^(-(d.a:ℝ)) *
      (∫ r in Icc (-((2:ℝ)^d.a)) ((2:ℝ)^d.a), ‖charFun d.weightedDistance r‖^2) ≤
        2*((2:ℝ)^d.N)^(12*d.lam) := by
  let := hd.probability
  let := d.weightedDistance_isFinite hQ hs
  have hm := d.weightedDistance_profile_mass hd hQ hs ha hX hY
  have hb : ∀ r : ℝ, ‖charFun d.weightedDistance r‖^2 ≤ ((2:ℝ)^d.N)^(12*d.lam) := by
    intro r
    have h := pow_le_pow_left₀ (norm_nonneg _) ((norm_charFun_le r).trans hm) 2
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ (2:ℝ)^d.N) (6*d.lam) 2] at h
    convert h using 1
    congr 1
    ring
  have hi : IntegrableOn (fun r => ‖charFun d.weightedDistance r‖^2)
      (Icc (-((2:ℝ)^d.a)) ((2:ℝ)^d.a)) := by
    simpa only [one_mul,IntegrableOn] using charFun_sq_integrable_finite d.weightedDistance
      (volume.restrict (Icc (-((2:ℝ)^d.a)) ((2:ℝ)^d.a))) 1
  have h := integral_mono hi (integrable_const (((2:ℝ)^d.N)^(12*d.lam))) hb
  rw [integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (neg_le_self (by positivity)))] at h
  have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ (2:ℝ)^(-(d.a:ℝ)) by positivity)
  apply h'.trans_eq
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
  field_simp
  ring

end PositiveDistanceData

end PlanarFalconer

end OAI
