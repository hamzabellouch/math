import OAI.NumberTheory.Ostmann.Supply.ActualKernelPairSum

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter

theorem eventually_sqrt_loss_le {e : ℝ} (he : 0<e) (C : ℝ) :
    ∀ᶠL:ℝ in atTop,C*Real.sqrt L≤e*L := by
  filter_upwards [Real.tendsto_sqrt_atTop.eventually_ge_atTop (C/e),
    eventually_ge_atTop (0:ℝ)] with L hs hL
  have hC : C≤e*Real.sqrt L := by exact (div_le_iff₀ he).mp hs |>.trans_eq (mul_comm _ _)
  have hm := mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg L)
  nlinarith [Real.sq_sqrt hL]

theorem eventually_pair_factor_small (C : ℝ) {η : ℝ} (hη : 0<η) :
    ∀ᶠL:ℝ in atTop,∀H Z:ℝ,(17/25:ℝ)*L≤H → 0<Z → Z≤2*Real.exp L →
      4718592*Real.exp (-(8/5:ℝ)*H+C*Real.sqrt L)≤η/Z := by
  have hdec : Tendsto (fun L:ℝ => (9437184:ℝ)*Real.exp (-(11/250:ℝ)*L)) atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(11/250:ℝ)<0))).const_mul (9437184:ℝ)
  filter_upwards [eventually_sqrt_loss_le (by norm_num : (0:ℝ)<11/250) C,
    hdec.eventually_le_const hη] with L hs hd
  intro H Z hH hZ hZup
  apply (le_div_iff₀ hZ).mpr
  have he : -(8/5:ℝ)*H+C*Real.sqrt L≤-(261/250:ℝ)*L := by linarith
  calc
    _ ≤ (4718592*Real.exp (-(261/250:ℝ)*L))*(2*Real.exp L) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num))
        hZup hZ.le (by positivity)
    _ = 9437184*Real.exp (-(11/250:ℝ)*L) := by
      rw [show -(11/250:ℝ)*L=-(261/250:ℝ)*L+L by ring,Real.exp_add]
      ring
    _ ≤ η := hd

end Ostmann.Supply

end

end OAI
