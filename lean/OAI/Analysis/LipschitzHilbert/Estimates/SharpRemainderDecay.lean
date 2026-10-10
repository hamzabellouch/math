import OAI.Analysis.LipschitzHilbert.Fourier.SharpBandHigh
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Exact restricted-mass algebra and exponential absorption for the
analytic remainders in the actual sharp Hilbert estimate. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem sqrt_product_of_ratio (F E ratio : ℝ) (hF : 0<F) (hr : 0<ratio)
    (heq : E=ratio^2*F) : Real.sqrt F*Real.sqrt E=ratio*F := by
  rw [heq,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hr]
  nlinarith [Real.mul_self_sqrt hF.le]

theorem restricted_power_ratio (F E ratio L a b : ℝ) (hF : 0<F) (hr : 0<ratio)
    (heq : E=ratio^2*F) (hlog : Real.log ratio=L) (hab : a+b=1) :
    F^a*E^b=Real.exp ((b-a)*L)*Real.sqrt F*Real.sqrt E := by
  have hE : 0<E := heq ▸ mul_pos (pow_pos hr 2) hF
  have hlogE : Real.log E=2*L+Real.log F := by
    rw [heq,Real.log_mul (pow_pos hr 2).ne' hF.ne',Real.log_pow,hlog]
    ring
  have hratio : ratio=Real.exp L := by rw [←hlog,Real.exp_log hr]
  have ha : a=1-b := by linarith
  calc
    _ = Real.exp (Real.log F*a+Real.log E*b) := by
      rw [Real.rpow_def_of_pos hF,Real.rpow_def_of_pos hE,Real.exp_add]
    _ = Real.exp ((b-a)*L)*Real.exp L*F := by
      rw [←Real.exp_log hF,←Real.exp_add,←Real.exp_add,hlogE,ha,Real.log_exp]
      congr 1
      ring
    _ = _ := by
      rw [←hratio]
      calc
        _ = Real.exp ((b-a)*L)*(ratio*F) := by ring
        _ = Real.exp ((b-a)*L)*(Real.sqrt F*Real.sqrt E) := by
          rw [sqrt_product_of_ratio F E ratio hF hr heq]
        _ = _ := by ring

theorem smaller_mass_ratio (F E ratio L : ℝ) (hF : 0<F) (hr : 0<ratio)
    (heq : E=ratio^2*F) (hlog : Real.log ratio=L) :
    min (4*F) E≤4*Real.exp (-L)*(Real.sqrt F*Real.sqrt E) := by
  rw [sqrt_product_of_ratio F E ratio hF hr heq]
  have hratio : ratio=Real.exp L := by rw [←hlog,Real.exp_log hr]
  rw [hratio]
  calc
    min (4*F) E ≤ 4*F := min_le_left _ _
    _ = _ := by rw [mul_assoc,←mul_assoc (Real.exp (-L)),←Real.exp_add]; ring_nf; simp

theorem eventually_remainder_decay (K Q : ℝ) (hK : 0≤K) :
    ∀ᶠ L : ℝ in atTop,
      4*K*(1+L)*Real.exp (-L)+Q*Real.exp (-L/3)≤L^(-19:ℝ) := by
  have hfast := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 20 1 (by norm_num)
  have hslow := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 19 (1/3) (by norm_num)
  have ht : Tendsto (fun L : ℝ => 8*K*(L^(20:ℝ)*Real.exp (-L))+
      Q*(L^(19:ℝ)*Real.exp (-L/3))) atTop (nhds 0) := by
    simpa only [one_mul,mul_zero,add_zero,neg_mul,one_div_mul_eq_div,neg_div] using
      (hfast.const_mul (8*K)).add (hslow.const_mul Q)
  filter_upwards [eventually_ge_atTop (1:ℝ), ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
    with L hL hsmall
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hp : 0<L^(19:ℝ) := Real.rpow_pos_of_pos hLp _
  have heq : L^(20:ℝ)=L^(19:ℝ)*L := by
    rw [show (20:ℝ)=19+1 by norm_num,Real.rpow_add hLp,Real.rpow_one]
  have hpre : (4*K*(1+L)*Real.exp (-L)+Q*Real.exp (-L/3))*L^(19:ℝ)≤1 := by
    have hfirst : 4*K*(1+L)*Real.exp (-L)*L^(19:ℝ)≤
        8*K*(L^(20:ℝ)*Real.exp (-L)) := by
      rw [heq]
      have hfactor : 0≤K*Real.exp (-L)*L^(19:ℝ) := by positivity
      nlinarith
    nlinarith
  rw [Real.rpow_neg hLp.le,←one_div]
  exact (le_div_iff₀ hp).2 hpre

theorem absorb_sharp_remainders (z : ℂ) (A K Q F E ratio L : ℝ)
    (hK : 0≤K) (hL : 0≤L) (hF : 0<F) (hr : 0<ratio)
    (heq : E=ratio^2*F) (hlog : Real.log ratio=L)
    (hdecay : 4*K*(1+L)*Real.exp (-L)+Q*Real.exp (-L/3)≤L^(-19:ℝ))
    (hbound : ‖z‖≤A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+
      K*(1+L)*min (4*F) E+Q*F^(2/3:ℝ)*E^(1/3:ℝ)) :
    ‖z‖≤(A+1)*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  have hm := smaller_mass_ratio F E ratio L hF hr heq hlog
  have hp := restricted_power_ratio F E ratio L (2/3) (1/3) hF hr heq hlog (by norm_num)
  have hp' : F^(2/3:ℝ)*E^(1/3:ℝ)=Real.exp (-L/3)*Real.sqrt F*Real.sqrt E := by
    have hexp : ((1/3:ℝ)-2/3)*L= -L/3 := by ring
    simpa only [hexp] using hp
  have hs : 0≤Real.sqrt F*Real.sqrt E := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    ‖z‖ ≤ A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+
        K*(1+L)*(4*Real.exp (-L)*(Real.sqrt F*Real.sqrt E))+
        Q*(Real.exp (-L/3)*Real.sqrt F*Real.sqrt E) := by
      rw [mul_assoc Q (F^(2/3:ℝ)),hp'] at hbound
      exact hbound.trans (add_le_add
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hm (by positivity))) le_rfl)
    _ = A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+
        (4*K*(1+L)*Real.exp (-L)+Q*Real.exp (-L/3))*(Real.sqrt F*Real.sqrt E) := by ring
    _ ≤ A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E+
        L^(-19:ℝ)*(Real.sqrt F*Real.sqrt E) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hdecay hs)
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
