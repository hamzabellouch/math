import OAI.Analysis.CircleDomains.Reflection.RoundReflectionDifferential

namespace OAI

/-! Elementary fixed-point equations for circular reflections and their
fractional-linear conjugates. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

lemma fractional_fixed_iff {a A z : ℂ} (hz : z≠a) :
    star a+A/(z-a)=star z ↔ A=((‖z-a‖^2 : ℝ) : ℂ) := by
  have hn : z-a≠0 := sub_ne_zero.mpr hz
  have hm : star (z-a)*(z-a)=((‖z-a‖^2 : ℝ) : ℂ) := by
    convert Complex.conj_mul' (z-a) using 1
    · rfl
    · rw [Complex.ofReal_pow]
  constructor
  · intro h
    have hd : A/(z-a)=star (z-a) := by rw [star_sub]; linear_combination h
    exact ((div_eq_iff hn).mp hd).trans hm
  · intro h
    have hd : A/(z-a)=star (z-a) := (div_eq_iff hn).mpr (h.trans hm.symm)
    rw [hd,star_sub]
    ring

lemma roundReflectionPlane_fixed_iff {c z : ℂ} {r : ℝ} (hr : 0<r) (hz : z≠c) :
    roundReflectionPlane c r z=z ↔ z∈sphere c r := by
  have hn : star (z-c)≠0 := star_ne_zero.mpr (sub_ne_zero.mpr hz)
  have hm : (z-c)*star (z-c)=((‖z-c‖^2 : ℝ) : ℂ) := by
    convert Complex.mul_conj' (z-c) using 1
    · rfl
    · rw [Complex.ofReal_pow]
  rw [roundReflectionPlane,mem_sphere,dist_eq_norm]
  constructor
  · intro h
    have hd : (r:ℂ)^2/star (z-c)=z-c := by linear_combination h
    have hs : (r:ℂ)^2=((‖z-c‖^2 : ℝ) : ℂ) := ((div_eq_iff hn).mp hd).trans hm
    have hs' : r^2=‖z-c‖^2 := by exact_mod_cast hs
    nlinarith [norm_nonneg (z-c)]
  · intro h
    have hd : (r:ℂ)^2/star (z-c)=z-c := by
      apply (div_eq_iff hn).mpr
      rw [hm,h]
      simp
    rw [hd,add_sub_cancel]

end CircleDomainRigidity

end

end OAI
