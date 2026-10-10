import Mathlib
import OAI.Analysis.CoulombRadii.Screening.ScreenUnits
import OAI.Analysis.CoulombRadii.RandomFields.EventTiltWavefunction

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma tendsto_positive_rpow_zero {q : ℝ} (hq : 0<q) :
    Tendsto (fun r : ℝ => r^q) (𝓝[>] 0) (𝓝 0) := by
  simpa [Real.zero_rpow hq.ne'] using
    ((Real.continuous_rpow_const hq.le).tendsto 0).mono_left nhdsWithin_le_nhds

def singleObservationOffset (D r : ℝ) : ℝ :=
  D+observationEventEnergyConstant*((r^(101/100:ℝ))⁻¹)^2*(1-Real.log (r^40))^5

lemma singleObservationOffset_scaled_tendsto (D : ℝ) :
    Tendsto (fun r => singleObservationOffset D r*r^7) (𝓝[>] 0) (𝓝 0) := by
  have ht := (tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<249/250)).sub
    ((tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0:ℝ)<249/250)).const_mul 40)
  have hpow : Tendsto (fun r : ℝ => r^7) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0)).pow 7
  have hh := (hpow.const_mul D).add ((ht.pow 5).const_mul observationEventEnergyConstant)
  simp only [mul_zero,sub_self,zero_pow (by decide : 5≠0),add_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr : 0<r := hr
  have hpn : r^(101/100:ℝ)≠0 := (Real.rpow_pos_of_pos hr _).ne'
  have hmul : (r^(249/250:ℝ))^5*(r^(101/100:ℝ))^2=r^7 := by
    rw [←Real.rpow_natCast (r^(249/250:ℝ)) 5,←Real.rpow_mul hr.le,
      ←Real.rpow_natCast (r^(101/100:ℝ)) 2,←Real.rpow_mul hr.le,←Real.rpow_add hr]
    norm_num
  have hratio : ((r^(101/100:ℝ))⁻¹)^2*r^7=(r^(249/250:ℝ))^5 := by
    rw [←hmul]
    field_simp
  dsimp [singleObservationOffset]
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  calc
    D*r^7+observationEventEnergyConstant*(r^(249/250:ℝ)-40*(Real.log r*r^(249/250:ℝ)))^5 =
      D*r^7+observationEventEnergyConstant*(r^(249/250:ℝ))^5*(1-40*Real.log r)^5 := by ring
    _ = _ := by rw [←hratio]; ring

lemma screenMass_small_offset {D r : ℝ} (hr : 0<r) (hr1 : r ≤ 1)
    (hD : 0 ≤ D) (hsmall : D*r^7 ≤ 1) :
    Coulomb.screenMass D r ≤ 2/r^3 := by
  have hr3 : 0<r^3 := pow_pos hr _
  have hb : Coulomb.screenBaseMass r=(r^3)⁻¹ := by
    unfold Coulomb.screenBaseMass
    apply max_eq_left
    exact (one_le_inv₀ hr3).mpr (pow_le_one₀ hr.le hr1)
  have hs : Real.sqrt (D*r) ≤ (r^3)⁻¹ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (inv_nonneg.mpr hr3.le)).mp
    rw [Real.sq_sqrt (mul_nonneg hD hr.le), inv_pow, inv_eq_one_div,
      le_div_iff₀ (pow_pos hr3 _)]
    nlinarith [hsmall]
  unfold Coulomb.screenMass
  rw [hb]
  calc
    (r^3)⁻¹+Real.sqrt (D*r) ≤ (r^3)⁻¹+(r^3)⁻¹ := add_le_add le_rfl hs
    _ = 2/r^3 := by ring

lemma observation_displacement_ratio_tendsto :
    Tendsto (fun r : ℝ => Real.sqrt 3*r^(101/100:ℝ)/r) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<1/100)).const_mul (Real.sqrt 3)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr : 0<r := hr
  have hx : r^(101/100:ℝ)/r=r^((101/100:ℝ)-1) := by rw [Real.rpow_sub hr,Real.rpow_one]
  rw [mul_div_assoc,hx]
  norm_num

end NeutralAtom
end

end
end

end OAI
