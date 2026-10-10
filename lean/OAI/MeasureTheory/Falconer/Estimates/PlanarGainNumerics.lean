import OAI.MeasureTheory.Falconer.Estimates.SamplingScales

namespace OAI

/-!
# Absorbing the explicit losses in the planar measure obstruction

Only fixed constants, logarithms and ceilings are absorbed here. The
underlying incidence estimate has already been proved from the cited
published input.
-/

namespace Falconer
open Real Filter
open scoped Topology

theorem samplingBallLoss_le {δ η B s : ℝ} (hB : B ≤ δ^(-η)) :
    samplingBallLoss (δ^(-η)) B s ≤ (exp 1 * 8^s) * δ^(-η) := by
  unfold samplingBallLoss
  have hh : (exp 1-1)*δ^(-η)+B ≤ exp 1*δ^(-η) := by linarith
  calc
    _ ≤ (exp 1*δ^(-η))*8^s := mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by ring

theorem rpow_absorb_constant {δ t u C : ℝ} (hδ : 0 < δ)
    (hC : C ≤ δ^(-(u-t))) : C * δ^(-t) ≤ δ^(-u) := by
  calc
    _ ≤ δ^(-(u-t)) * δ^(-t) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring

theorem sampling_point_loss_le {δ η Tf C : ℝ} (hδ : 0 < δ)
    (hTf : 0 ≤ Tf) (hT : Tf ≤ C*δ^(-η)) :
    2*(8*Tf/δ^η)^2 ≤ (128*C^2)*δ^(-4*η) := by
  have hh : 0 ≤ 8*Tf/δ^η := by positivity
  have hq : 8*Tf/δ^η ≤ 8*(C*δ^(-η))/δ^η := by gcongr
  have he : (δ^(-η)/δ^η)^2 = δ^(-4*η) := by
    rw [← Real.rpow_sub hδ, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    ring
  calc
    _ ≤ 2*(8*(C*δ^(-η))/δ^η)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh hq 2) (by norm_num)
    _ = (128*C^2)*(δ^(-η)/δ^η)^2 := by ring
    _ = _ := by rw [he]

theorem sampling_direction_loss_le {δ η Tb C b : ℝ} (hδ : 0 < δ)
    (hTb : 0 ≤ Tb) (hT : Tb ≤ C*δ^(-η)) :
    8*2^b*Tb^2/δ^η ≤ (8*2^b*C^2)*δ^(-3*η) := by
  have he : (δ^(-η))^2/δ^η = δ^(-3*η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_sub hδ]
    congr 1
    ring
  calc
    _ ≤ 8*2^b*(C*δ^(-η))^2/δ^η := by gcongr
    _ = (8*2^b*C^2)*((δ^(-η))^2/δ^η) := by ring
    _ = _ := by rw [he]

structure PlanarSamplingReady (δ b f η ε : ℝ) (J : ℕ) : Prop where
  scale_pos : 0 < δ
  scale_small : δ ≤ 1/4
  budget : 1 ≤ -10*log δ
  point_loss : 2*(8*samplingBallLoss (δ^(-η)) (-10*log δ) f/δ^η)^2 ≤ δ^(-ε)
  direction_loss : 8*2^b*(samplingBallLoss (δ^(-η)) (-10*log δ) b)^2/δ^η ≤ δ^(-ε)
  count : (Nat.ceil (δ^(-b)) : ℝ) ≤ δ^(-b-ε/4)
  cover : (δ^(-b-η)) * (2*J+1) ≤ δ^(-b-ε/4)
  tail : (((2 * Nat.ceil (δ⁻¹+1)+1)^2 * Nat.ceil δ⁻¹ : ℕ) : ℝ) *
    exp (-(-10*log δ)) ≤ δ^η/16

theorem eventually_planarSamplingReady {b f η ε : ℝ} (hb : 0 < b)
    (hη : 0 < η) (hη1 : η ≤ 1) (hmargin : 4*η < ε)
    (J : ℕ) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), PlanarSamplingReady δ b f η ε J := by
  let Cf := exp 1 * (8 : ℝ)^f
  let Cb := exp 1 * (8 : ℝ)^b
  have hp := (tendsto_rpow_neg_nhdsGT_zero (show -(ε-4*η) < 0 by linarith)).eventually
    (eventually_ge_atTop (128*Cf^2))
  have ht := (tendsto_rpow_neg_nhdsGT_zero (show -(ε-3*η) < 0 by linarith)).eventually
    (eventually_ge_atTop (8*2^b*Cb^2))
  have hn := (tendsto_rpow_neg_nhdsGT_zero (show -(ε/4) < 0 by linarith)).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hc := (tendsto_rpow_neg_nhdsGT_zero (show -(ε/4-η) < 0 by linarith)).eventually
    (eventually_ge_atTop (2*J+1 : ℝ))
  filter_upwards [sampling_log_budget hη, hp, ht, hn, hc,
    Ioc_mem_nhdsGT (show (0 : ℝ) < 1/4 by norm_num),
    Ioc_mem_nhdsGT (exp_pos (-1 : ℝ))] with δ hlog hp ht hn hc hδsmall hδexp
  have hδ : 0 < δ := hδsmall.1
  have hδ1 : δ ≤ 1 := hδsmall.2.trans (by norm_num)
  have hB : 1 ≤ -10*log δ := by
    have hh := Real.log_le_log hδ hδexp.2
    rw [Real.log_exp] at hh
    linarith
  have hT (s : ℝ) : 0 < samplingBallLoss (δ^(-η)) (-10*log δ) s :=
    samplingBallLoss_pos (by positivity) hB
  refine ⟨hδ, hδsmall.2, hB, ?_, ?_, ?_, ?_, ?_⟩
  · apply (sampling_point_loss_le hδ (hT f).le (samplingBallLoss_le hlog)).trans
    simpa only [Cf, neg_mul] using rpow_absorb_constant hδ hp
  · apply (sampling_direction_loss_le hδ (hT b).le (samplingBallLoss_le hlog)).trans
    simpa only [Cb, neg_mul] using rpow_absorb_constant hδ ht
  · have hsize := (sampling_ceil_size hδ hδ1 hb.le).2.2
    have hN : (Nat.ceil (δ^(-b)) : ℝ) ≤ 2*δ^(-b) := by
      have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hδ b)).mpr hsize
      simpa only [Real.rpow_neg hδ.le, div_eq_mul_inv] using hh
    apply hN.trans
    have hh := rpow_absorb_constant (t := b) (u := b+ε/4) hδ
      (by simpa only [add_sub_cancel_left] using hn)
    convert hh using 1; ring_nf
  · have hh := rpow_absorb_constant (t := b+η) (u := b+ε/4) hδ
      (by convert hc using 1; ring_nf)
    convert hh using 1 <;> ring_nf
  · apply (sampling_failure_bound hδ hδsmall.2).trans
    apply div_le_div_of_nonneg_right _ (by norm_num)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη1

end Falconer

end OAI
