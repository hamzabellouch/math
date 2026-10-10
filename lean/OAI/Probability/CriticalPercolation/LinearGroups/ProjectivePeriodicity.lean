import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.PowerBoundedUnipotent

namespace OAI

section
noncomputable section
open Module

namespace CriticalPercolation.LinearGrowth
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

def continuousEndAlgEquiv : End ℂ V ≃ₐ[ℂ] (V →L[ℂ] V) :=
  AlgEquiv.ofLinearEquiv LinearMap.toContinuousLinearMap rfl (fun _ _ => rfl)

omit [FiniteDimensional ℂ V] in
lemma scalar_power_of_projective_bound (T : V →L[ℂ] V)
    (δ : ℝ) (hδ : 0<δ)
    (hb : ∀ n : ℕ, ∀ x : V, δ*‖T^n‖*‖x‖≤‖(T^n) x‖)
    {v : V} (hv : v≠0) {a : ℂ} (ha : a≠0) (he : T v=a • v)
    (m : ℕ) (hni : IsNilpotent (T^m-a^m • (1:V →L[ℂ] V))) :
    T^m=a^m • (1:V →L[ℂ] V) := by
  let U := (a^m)⁻¹ • T^m
  have hU : IsNilpotent (U-1) := by
    have hh := hni.smul ((a^m)⁻¹)
    simpa only [U,smul_sub,smul_smul,inv_mul_cancel₀ (pow_ne_zero m ha),one_smul] using hh
  have hepow (n : ℕ) : (T^n) v=a^n • v := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      change T ((T^n) v)=_
      rw [ih,map_smul,he,smul_smul,pow_succ]
  have hnorm (n : ℕ) : δ*‖T^n‖≤‖a‖^n := by
    have hh := hb n v
    rw [hepow,norm_smul,norm_pow a n] at hh
    exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv)).mp hh
  have hUb (n : ℕ) : ‖U^n‖≤1/δ := by
    dsimp [U]
    rw [smul_pow,norm_smul,norm_pow ((a^m)⁻¹) n,norm_inv,norm_pow a m,inv_pow,←pow_mul,←pow_mul]
    have hh := hnorm (m*n)
    have hpos : 0<‖a‖^(m*n) := pow_pos (norm_pos_iff.mpr ha) _
    rw [inv_mul_eq_div]
    apply (div_le_div_iff₀ hpos hδ).mpr
    nlinarith
  have hU1 : U=1 := eq_one_of_power_bounded_unipotent U hU (1/δ) hUb
  have hh := congrArg (fun x : V →L[ℂ] V => a^m • x) hU1
  simpa only [U,smul_smul,mul_inv_cancel₀ (pow_ne_zero m ha),one_smul] using hh

end CriticalPercolation.LinearGrowth
end
end

end OAI
