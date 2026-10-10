import Mathlib
import OAI.Analysis.CoulombRadii.Screening.ScreeningNormalization

namespace OAI

section
section
noncomputable section
namespace Coulomb

def screenMass (δ a : ℝ) : ℝ := screenBaseMass a+Real.sqrt (δ*a)
def screenEnergy (δ a : ℝ) : ℝ := (screenMass δ a)^2/a

lemma screenMass_ge_base (δ a : ℝ) : screenBaseMass a ≤ screenMass δ a := by
  unfold screenMass
  linarith [Real.sqrt_nonneg (δ*a)]
lemma screenMass_ge_one (δ a : ℝ) : 1 ≤ screenMass δ a :=
  (screenBaseMass_ge_one a).trans (screenMass_ge_base δ a)
lemma screenMass_pos (δ a : ℝ) : 0<screenMass δ a := lt_of_lt_of_le zero_lt_one (screenMass_ge_one δ a)
lemma screenMass_scale (δ : ℝ) {a : ℝ} (ha : 0<a) : 1 ≤ a*screenMass δ a :=
  (screenBaseMass_scale ha).trans (mul_le_mul_of_nonneg_left (screenMass_ge_base δ a) ha.le)
lemma screenEnergy_pos (δ : ℝ) {a : ℝ} (ha : 0<a) : 0<screenEnergy δ a :=
  div_pos (sq_pos_of_pos (screenMass_pos δ a)) ha
lemma screenEnergy_ge_offset {δ a : ℝ} (hδ : 0 ≤ δ) (ha : 0<a) : δ ≤ screenEnergy δ a := by
  rw [screenEnergy,le_div_iff₀ ha]
  have hm : Real.sqrt (δ*a) ≤ screenMass δ a := by
    unfold screenMass
    linarith [screenBaseMass_nonneg a]
  have H := pow_le_pow_left₀ (Real.sqrt_nonneg (δ*a)) hm 2
  rwa [Real.sq_sqrt (mul_nonneg hδ ha.le)] at H

lemma screenBaseMass_comparable {a b q : ℝ} (ha : 0<a) (hq : 1 ≤ q)
    (hab : a/q ≤ b) : screenBaseMass b ≤ q^3*screenBaseMass a := by
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hb : 0<b := lt_of_lt_of_le (div_pos ha hq0) hab
  have H : a ≤ b*q := (div_le_iff₀ hq0).mp hab
  have H3 := pow_le_pow_left₀ ha.le H 3
  have Hi : (b^3)⁻¹ ≤ q^3*(a^3)⁻¹ := by
    calc
      (b^3)⁻¹=q^3/(b*q)^3 := by field_simp
      _ ≤ q^3/a^3 := div_le_div_of_nonneg_left (pow_nonneg hq0.le _) (pow_pos ha _) H3
      _ = q^3*(a^3)⁻¹ := div_eq_mul_inv _ _
  apply max_le
  · exact Hi.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (pow_nonneg hq0.le 3))
  · exact (one_le_pow₀ hq).trans (le_mul_of_one_le_right (pow_nonneg hq0.le 3) (screenBaseMass_ge_one a))

lemma screenMass_comparable {δ a b q : ℝ} (hδ : 0 ≤ δ) (ha : 0<a) (hq : 1 ≤ q)
    (hab : a/q ≤ b) (hba : b ≤ a*q) : screenMass δ b ≤ q^3*screenMass δ a := by
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hb : 0<b := lt_of_lt_of_le (div_pos ha hq0) hab
  have hq6 : q ≤ q^6 := by
    calc
      q=q^1 := by simp
      _ ≤ q^6 := pow_le_pow_right₀ hq (by omega)
  have hroot : Real.sqrt (δ*b) ≤ q^3*Real.sqrt (δ*a) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [mul_pow,Real.sq_sqrt (mul_nonneg hδ ha.le)]
      have hb' : b ≤ a*q^6 := hba.trans (mul_le_mul_of_nonneg_left hq6 ha.le)
      nlinarith [mul_le_mul_of_nonneg_left hb' hδ]
  unfold screenMass
  nlinarith [screenBaseMass_comparable ha hq hab]

lemma screenEnergy_comparable {δ a b q : ℝ} (hδ : 0 ≤ δ) (ha : 0<a) (hq : 1 ≤ q)
    (hab : a/q ≤ b) (hba : b ≤ a*q) : screenEnergy δ b ≤ q^7*screenEnergy δ a := by
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hb : 0<b := lt_of_lt_of_le (div_pos ha hq0) hab
  have H := screenMass_comparable hδ ha hq hab hba
  have H2 := pow_le_pow_left₀ (screenMass_pos δ b).le H 2
  unfold screenEnergy
  calc
    (screenMass δ b)^2/b ≤ (q^3*screenMass δ a)^2/(a/q) :=
      div_le_div₀ (sq_nonneg _) H2 (div_pos ha hq0) hab
    _ = q^7*((screenMass δ a)^2/a) := by field_simp

end Coulomb
end

end
end

end OAI
