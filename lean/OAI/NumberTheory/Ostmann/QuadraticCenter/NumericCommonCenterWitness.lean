import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericCommonCenterMargins

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
namespace CommonCenterElementaryBounds
variable {X Z J k : ℕ} (h : CommonCenterElementaryBounds X Z J k)
include h

theorem multiplier_pos : 0 < quadraticLiftMultiplierBound Z := by
  apply Nat.ceil_pos.mpr
  exact Real.rpow_pos_of_pos h.Z_pos _

theorem multiplier_lt : quadraticLiftMultiplierBound Z < Z := by
  have hA := quadraticLiftMultiplierBound_le Z (by have := h.Z_two_le; omega)
  have hlarge : (2:ℝ)<(Z:ℝ)^(87/100:ℝ) := by
    have := h.rpow_large (a:=87/100) (by norm_num)
    linarith
  have hh := mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos h.Z_pos (13/100:ℝ))
  rw [←Real.rpow_add h.Z_pos] at hh
  norm_num at hh
  exact_mod_cast hA.trans_lt hh

theorem weighted_count_lower {C : ℝ} {K : ℕ}
    (hcost : C*(K:ℝ) ≤ Real.log Z/1000) :
    2*commonCenterMomentScale J Z k*(quadraticLiftMultiplierBound Z:ℝ) ≤
      Real.exp (-C*K)*(J.descFactorial k:ℝ) := by
  have hA := quadraticLiftMultiplierBound_le Z (by have := h.Z_two_le; omega)
  have he : (Z:ℝ)^(-(1/1000:ℝ)) ≤ Real.exp (-C*K) := by
    rw [Real.rpow_def_of_pos h.Z_pos]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlarge : (8:ℝ)≤(Z:ℝ)^(9/1000:ℝ) := by
    have := h.rpow_large (a:=9/1000) (by norm_num)
    linarith
  have hh := mul_le_mul_of_nonneg_right hlarge
    (Real.rpow_nonneg h.Z_pos.le (-(1/100:ℝ)))
  rw [←Real.rpow_add h.Z_pos] at hh
  norm_num at hh
  have hid : (Z:ℝ)^(-(7/50:ℝ))*(Z:ℝ)^(13/100:ℝ) =
      (Z:ℝ)^(-(1/100:ℝ)) := by
    rw [←Real.rpow_add h.Z_pos]
    norm_num
  have hscale : 0≤commonCenterMomentScale J Z k := by
    unfold commonCenterMomentScale
    positivity
  calc
    _ ≤ 2*commonCenterMomentScale J Z k*(2*(Z:ℝ)^(13/100:ℝ)) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    _ = 4*(J:ℝ)^k*(Z:ℝ)^(-(1/100:ℝ)) := by
      unfold commonCenterMomentScale
      calc
        _ = 4*(J:ℝ)^k*((Z:ℝ)^(-(7/50:ℝ))*(Z:ℝ)^(13/100:ℝ)) := by ring
        _ = _ := by rw [hid]
    _ ≤ (Z:ℝ)^(-(1/1000:ℝ))*((J:ℝ)^k/2) := by
      have := mul_le_mul_of_nonneg_right hh (pow_nonneg (Nat.cast_nonneg J) k)
      nlinarith
    _ ≤ Real.exp (-C*K)*(J.descFactorial k:ℝ) :=
      mul_le_mul he h.descFactorial_half (by positivity) (by positivity)

theorem event_quotient_lower {C : ℝ} {K E : ℕ}
    (hcost : C*(K:ℝ) ≤ Real.log Z/1000)
    (hprob : Real.exp (-C*K) ≤ (E:ℝ)/(J.choose k:ℝ)) :
    commonCenterMomentScale J Z k ≤ (k.factorial*E/quadraticLiftMultiplierBound Z:ℕ) := by
  have hJpos : (0:ℝ)<J := lt_of_lt_of_le zero_lt_one h.J_one_le
  have hdescpos : (0:ℝ)<(J.descFactorial k:ℝ) :=
    lt_of_lt_of_le (by positivity) h.descFactorial_half
  have hchoosepos : (0:ℝ)<(J.choose k:ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul] at hdescpos
    have hf : (0:ℝ)<(k.factorial:ℝ) := by exact_mod_cast k.factorial_pos
    nlinarith
  have hp := (le_div_iff₀ hchoosepos).mp hprob
  have hf : (0:ℝ)≤(k.factorial:ℝ) := Nat.cast_nonneg _
  have hp' := mul_le_mul_of_nonneg_left hp hf
  have hcount : Real.exp (-C*K)*(J.descFactorial k:ℝ) ≤ (k.factorial*E:ℕ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul,Nat.cast_mul]
    nlinarith
  have hlower := (h.weighted_count_lower hcost).trans hcount
  let A := quadraticLiftMultiplierBound Z
  let N := k.factorial*E
  have hApos : (0:ℝ)<A := by exact_mod_cast h.multiplier_pos
  have hrem : ((N%A:ℕ):ℝ)<A := by exact_mod_cast Nat.mod_lt N h.multiplier_pos
  have hdiv : (N:ℝ)=(A:ℝ)*((N/A:ℕ):ℝ)+((N%A:ℕ):ℝ) := by
    exact_mod_cast (Nat.div_add_mod N A).symm
  have hupper : (N:ℝ)<(A:ℝ)*(((N/A:ℕ):ℝ)+1) := by nlinarith
  have htwice : 2*commonCenterMomentScale J Z k < ((N/A:ℕ):ℝ)+1 := by
    have hprod : (A:ℝ)*(2*commonCenterMomentScale J Z k) < (A:ℝ)*(((N/A:ℕ):ℝ)+1) := by
      nlinarith [hlower]
    exact lt_of_mul_lt_mul_left hprod hApos.le
  have hlarge := h.momentScale_large
  change commonCenterMomentScale J Z k ≤ ((N/A:ℕ):ℝ)
  linarith

end CommonCenterElementaryBounds
end Ostmann.QuadraticCenter

end

end OAI
