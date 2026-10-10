import OAI.MeasureTheory.Falconer.Estimates.PacketParameterBounds
import OAI.MeasureTheory.Falconer.Estimates.SampledRowCardinality

namespace OAI

/-! The cardinality exponents in the packet theorem follow from the
polynomial loss bounds, including the two-level scale shift. -/
namespace Falconer

theorem shifted_packet_powers (N : ℕ) (s ε : ℝ) :
    Real.exp ((s-ε)*((N+2:ℕ):ℝ)*Real.log 2) =
      (4:ℝ)^s/(Real.exp (ε*((N+2:ℕ):ℝ)*Real.log 2)*(1/(2:ℝ)^N)^s) ∧
    Real.exp ((s+ε)*((N+2:ℕ):ℝ)*Real.log 2) =
      (4:ℝ)^s*Real.exp (ε*((N+2:ℕ):ℝ)*Real.log 2)/(1/(2:ℝ)^N)^s := by
  have hpow : (1/(2:ℝ)^N)^s = Real.exp (-s*(N:ℝ)*Real.log 2) := by
    simpa only [div_pow,one_pow] using half_power_rpow_exp N s
  have h4 : (4:ℝ)^s = Real.exp (2*s*Real.log 2) := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.rpow_def_of_pos (by positivity),Real.log_pow]
    congr 1
    ring
  rw [hpow,h4]
  constructor
  · rw [← Real.exp_add,← Real.exp_sub]
    congr 1
    push_cast
    ring
  · rw [← Real.exp_add,← Real.exp_sub]
    congr 1
    push_cast
    ring

theorem packet_cardinality_scales (N : ℕ) {s ε E KF J B m M : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hE : 1 ≤ E) (hKF : 1 ≤ KF) (hKFup : KF ≤ E)
    (hJ : 0 < J) (hJup : J ≤ E) (hB : 0 < B) (hBup : B ≤ E/(1/(2:ℝ)^N)^s)
    (hm : 1/(E*((1/(2:ℝ)^N)^s)^2) ≤ m)
    (hM : 0 < M) (hMup : M ≤ E/((1/(2:ℝ)^N)^s)^2)
    (hloss : 16*E^5 ≤ Real.exp (ε*((N+2:ℕ):ℝ)*Real.log 2)) :
    Real.exp ((s-ε)*((N+2:ℕ):ℝ)*Real.log 2) ≤ m/(4*J*B) ∧
    KF*(1/(2:ℝ)^N)^s*M ≤ Real.exp ((s+ε)*((N+2:ℕ):ℝ)*Real.log 2) ∧
    KF*(4*J*B*M/m) ≤ Real.exp (ε*((N+2:ℕ):ℝ)*Real.log 2)/(1/(2:ℝ)^N)^s := by
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  have hδs : 0 < (1/(2:ℝ)^N)^s := Real.rpow_pos_of_pos hδ _
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hE3 : E^3 ≤ E^5 := pow_le_pow_right₀ hE (by norm_num)
  have hE2 : E^2 ≤ E^5 := pow_le_pow_right₀ hE (by norm_num)
  have h4up : (4:ℝ)^s ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 4) hs1
  have h4lo : (1:ℝ) ≤ 4^s := Real.one_le_rpow (by norm_num) hs
  obtain ⟨hlo,hup,hreg,_⟩ := packet_parameter_bounds hδ hE hKF hKFup hJ hJup hB hBup hm hM hMup
  obtain ⟨hshiftlo,hshiftup⟩ := shifted_packet_powers N s ε
  refine ⟨?_,?_,?_⟩
  · rw [hshiftlo]
    apply le_trans _ hlo
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hL : 16*E^3 ≤ Real.exp (ε*((N+2:ℕ):ℝ)*Real.log 2) :=
      (mul_le_mul_of_nonneg_left hE3 (by norm_num)).trans hloss
    have hh := mul_le_mul_of_nonneg_left h4up (show 0 ≤ 4*E^3 by positivity)
    have hh' : (4:ℝ)^s*(4*E^3) ≤ Real.exp (ε*((N+2:ℕ):ℝ)*Real.log 2) := by
      nlinarith only [hh,hL]
    nlinarith only [mul_le_mul_of_nonneg_right hh' hδs.le]
  · apply hup.trans
    rw [hshiftup]
    apply div_le_div_of_nonneg_right _ hδs.le
    have hD : E^2 ≤ Real.exp (ε*((N+2:ℕ):ℝ)*Real.log 2) := by
      have hh : E^5 ≤ 16*E^5 := by nlinarith only [pow_nonneg hE0.le 5]
      exact hE2.trans (hh.trans hloss)
    exact hD.trans (le_mul_of_one_le_left (Real.exp_pos _).le h4lo)
  · exact hreg.trans (div_le_div_of_nonneg_right
      ((show 4*E^5 ≤ 16*E^5 by nlinarith only [pow_nonneg hE0.le 5]).trans hloss) hδs.le)

end Falconer

end OAI
