import OAI.NumberTheory.Ostmann.Conclusion.BadFraction
import OAI.NumberTheory.Ostmann.Conclusion.FinalRateAbsorptionScales
import OAI.NumberTheory.Ostmann.Conclusion.SymmetrizedNorm

namespace OAI

noncomputable section
namespace Ostmann.Conclusion
open Filter
open scoped Topology

theorem final_energy_absorption_of_bounds
    (R0 V E F A D B r m : ℝ) (hR0 : 0 ≤ R0) (hF : 0 ≤ F) (hr : 0 ≤ r) (hm : 0 ≤ m)
    (hcard : 2*V+1 ≤ 3*Real.exp E)
    (hbad : E+A+D ≤ -(2*B+3)*r*m)
    (hpre : 3*R0*(F+1) ≤ Real.exp (r*m)) :
    R0*(2*V+1)*(F*Real.exp A*Real.exp D+Real.exp (-(E+(2*B+3)*r*m))) ≤
      Real.exp (-(2*B+1)*r*m) := by
  have hid1 : Real.exp E*(F*Real.exp A*Real.exp D)=F*Real.exp (E+A+D) := by
    rw [Real.exp_add,Real.exp_add]
    ring
  have hid2 : Real.exp E*Real.exp (-(E+(2*B+3)*r*m))=Real.exp (-(2*B+3)*r*m) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ R0*(3*Real.exp E)*(F*Real.exp A*Real.exp D+Real.exp (-(E+(2*B+3)*r*m))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hR0) (by positivity)
    _ = 3*R0*(F*Real.exp (E+A+D)+Real.exp (-(2*B+3)*r*m)) := by
      calc
        _ = 3*R0*(Real.exp E*(F*Real.exp A*Real.exp D)+
            Real.exp E*Real.exp (-(E+(2*B+3)*r*m))) := by ring
        _ = _ := by rw [hid1,hid2]
    _ ≤ 3*R0*(F*Real.exp (-(2*B+3)*r*m)+Real.exp (-(2*B+3)*r*m)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbad) hF) le_rfl)
        (by positivity)
    _ = (3*R0*(F+1))*Real.exp (-(2*B+3)*r*m) := by ring
    _ ≤ Real.exp (r*m)*Real.exp (-(2*B+3)*r*m) :=
      mul_le_mul_of_nonneg_right hpre (Real.exp_pos _).le
    _ = Real.exp (-(2*B+2)*r*m) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hr hm])

theorem eventually_finalRate_absorption (Bs BD Bz B R0 C : ℝ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hR0 : 0 < R0)
    {k : ℕ} (hk : 2 ≤ k)
    (hrate : finalRate BD Bs Bz (C+2) k < -2*B-4) :
    ∀ᶠ L : ℝ in atTop,
      R0*(2*(frequencyBound Bs BD Bz k L k : ℝ)+1)*
        (((2 : ℝ)^k)^(2*(2^k))*
          Real.exp ((2-(3/4 : ℝ)*Real.log ((2 : ℝ)^k))*(2 : ℝ)^k*(bulkSize k L : ℝ))*
          Real.exp ((2 : ℝ)^k*(initialGap Bs k L+C*(bulkSize k L : ℝ))+(bulkSize k L : ℝ))+
          Real.exp (-(frequencyBudget Bs BD Bz k L k+(2*B+3)*(2 : ℝ)^k*(bulkSize k L : ℝ)))) ≤
        Real.exp (-(2*B+1)*(2 : ℝ)^k*(bulkSize k L : ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  filter_upwards [eventually_final_bad_exponent hBs hBD hBz B C hk1 hrate,
    eventually_final_prefactor R0 hk1] with L hbad hpre
  exact final_energy_absorption_of_bounds R0 (frequencyBound Bs BD Bz k L k)
    (frequencyBudget Bs BD Bz k L k) (((2 : ℝ)^k)^(2*(2^k)))
    ((2-(3/4 : ℝ)*Real.log ((2 : ℝ)^k))*(2 : ℝ)^k*(bulkSize k L : ℝ))
    ((2 : ℝ)^k*(initialGap Bs k L+C*(bulkSize k L : ℝ))+(bulkSize k L : ℝ))
    B ((2 : ℝ)^k) (bulkSize k L) hR0.le (by positivity) (by positivity) (by positivity)
    (frequency_card_le_exp hBs hBD hBz hk1 L k) hbad hpre

end Ostmann.Conclusion

end

end OAI
