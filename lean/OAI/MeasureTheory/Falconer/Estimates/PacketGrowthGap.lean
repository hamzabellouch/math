import OAI.MeasureTheory.Falconer.Estimates.PacketPolynomialLoss
import OAI.MeasureTheory.Falconer.Estimates.SampledRowCardinality

namespace OAI

/-! The frozen-packet upper bound contradicts the packet power gain
once the input weak exponent is chosen sufficiently small. -/
namespace Falconer

theorem packet_growth_gap {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C) :
    ∃ ε0 : ℝ, ∃ N0 : ℕ, 0 < ε0 ∧ 0 < N0 ∧
      ∀ (n : ℕ) (ε s B : ℝ), N0 ≤ n+2 → 0 ≤ ε → ε ≤ ε0 → 0 ≤ s →
      Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2) ≤ B →
      B ≤ C*(Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2))^6/((1/(2:ℝ)^n)^s)^2 → False := by
  obtain ⟨ε0,N0,hε0,hN0,hcost⟩ := packet_polynomial_loss (by positivity : 0 < η/2) hC
  refine ⟨ε0,N0,hε0,hN0,?_⟩
  intro n ε s B hn hε hεup hs hlo hup
  let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let E0 := Real.exp (ε0*((n+2:ℕ):ℝ)*Real.log 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdepth : (0:ℝ) < (n+2:ℕ) := by positivity
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hEE : E ≤ E0 := Real.exp_le_exp.mpr (by gcongr)
  have hE6 : E^6 ≤ E0^48 := (pow_le_pow_left₀ (Real.exp_pos _).le hEE _).trans
    (pow_le_pow_right₀ (hE.trans hEE) (by norm_num))
  have hc := (hcost (n+2) hn).2.2.2
  have hpoly : (1:ℝ) ≤ (((n+2:ℕ):ℝ)+1)^2 := one_le_pow₀ (by
    have := Nat.cast_nonneg (α := ℝ) (n+2)
    linarith)
  have hCE : C*E^6 ≤ Real.exp ((η/2)*((n+2:ℕ):ℝ)*Real.log 2) := by
    apply le_trans _ hc
    calc
      C*E^6 ≤ C*E0^48 := mul_le_mul_of_nonneg_left hE6 hC
      _ ≤ C*((((n+2:ℕ):ℝ)+1)^2)*E0^48 := by
        exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC hpoly) (pow_nonneg (Real.exp_pos _).le _)
  have hstrict : C*E^6 < Real.exp (η*((n+2:ℕ):ℝ)*Real.log 2) := hCE.trans_lt
    (Real.exp_lt_exp.mpr (by nlinarith only [mul_pos (mul_pos hη hdepth) hlog]))
  have hpow : (1/(2:ℝ)^n)^s = Real.exp (-s*(n:ℝ)*Real.log 2) := by
    simpa only [div_pow,one_pow] using half_power_rpow_exp n s
  have heq : Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2)*((1/(2:ℝ)^n)^s)^2 =
      Real.exp (η*((n+2:ℕ):ℝ)*Real.log 2+4*s*Real.log 2) := by
    rw [hpow,← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    push_cast
    ring
  have hscale : 0 < ((1/(2:ℝ)^n)^s)^2 := by positivity
  have hlower : Real.exp (η*((n+2:ℕ):ℝ)*Real.log 2) ≤
      Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2)*((1/(2:ℝ)^n)^s)^2 := by
    rw [heq]
    exact Real.exp_le_exp.mpr (le_add_of_nonneg_right (by positivity))
  have hupper : Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2)*((1/(2:ℝ)^n)^s)^2 ≤ C*E^6 :=
    (mul_le_mul_of_nonneg_right hlo hscale.le).trans ((le_div_iff₀ hscale).1 hup)
  exact hstrict.not_ge (hlower.trans hupper)

end Falconer

end OAI
