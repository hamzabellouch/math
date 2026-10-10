import OAI.NumberTheory.TotientAsymptotic.PrefixTerminalLower
import OAI.NumberTheory.TotientAsymptotic.UniformPrefactor
import OAI.NumberTheory.TotientAsymptotic.RenewalInput

namespace OAI

/-! The first positive-volume ingredient for the prime-family construction. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

theorem fixed_terminal_volume_lower (t : ℝ) (ht : 0 ≤ t) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ, N+1+H=m x →
      G x (N+1)/2 ≤ volume.real
        (prefixRegion (N+1) (B x) 0 0 ∩ {u | t ≤ u (Fin.last N)}) := by
  obtain ⟨C,hC,hstep⟩ := uniform_step_bound fordRenewalInput
  have hlim : Tendsto (fun H : ℕ => (2*C*t)*rho^H) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one rho_pos.le rho_lt_one).const_mul (2*C*t)
  filter_upwards [hlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
    with H hH
  filter_upwards [hstep,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hB
  intro N hNm
  have hHm : H ≤ m x := by omega
  have he : m x-H=N+1 := by omega
  have hh := hx H hHm
  rw [he] at hh
  have hb := mul_le_mul_of_nonneg_right hh (show 0 ≤ 2*t by positivity)
  have hsmall : (2*t)*(((N+1:ℕ):ℝ)*g (N+1)/B x) ≤ 1 := by
    calc
      _ ≤ (C*rho^H)*(2*t) := by simpa only [mul_comm] using hb
      _ ≤ 1 := by nlinarith only [hH.le]
  have hcost : 2*(N+1:ℝ)*g (N+1)*t ≤ B x := by
    have hh : (2*(N+1:ℝ)*g (N+1)*t)/B x ≤ 1 := by
      convert hsmall using 1
      push_cast
      ring
    exact (div_le_iff₀ hB).mp hh |>.trans_eq (one_mul _)
  exact prefix_terminal_volume_lower hB N ht hcost

end TotientAsymptotic

end

end OAI
