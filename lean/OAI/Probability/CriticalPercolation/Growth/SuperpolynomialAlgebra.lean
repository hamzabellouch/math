import Mathlib

namespace OAI

section
section
noncomputable section
open Filter Set
open scoped Topology

namespace CriticalPercolation

lemma clog_two_le_log (r : ℕ) (hr : 1≤r) :
    (Nat.clog 2 r:ℝ) ≤ Real.log r / Real.log 2 + 1 := by
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hclog : Nat.clog 2 r ≤ Nat.log 2 r+1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by norm_num : 1<(2:ℕ)) r).le
  have hp : (2:ℝ)^(Nat.log 2 r)≤(r:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : r≠0)
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<2^(Nat.log 2 r)) hp
  rw [Real.log_pow] at hlog
  have hh : (Nat.log 2 r:ℝ)≤Real.log r/Real.log 2 := (le_div_iff₀ h2).mpr hlog
  have hc : (Nat.clog 2 r:ℝ)≤(Nat.log 2 r:ℝ)+1 := by exact_mod_cast hclog
  linarith

lemma band_log_bound {c f : ℝ} (hc : 0<c) (s : ℕ) (hs : 2 ≤ s)
    (hf : (Real.log s)⁻¹^2≤f) :
    0<c*f ∧ Real.log (1/(c*f)) ≤ Real.log (1/c)+2*Real.log (Real.log s) := by
  have hls : 0<Real.log s := Real.log_pos (by exact_mod_cast hs)
  have hpos : 0<(Real.log s)⁻¹^2 := pow_pos (inv_pos.mpr hls) _
  have hfp : 0<f := hpos.trans_le hf
  refine ⟨mul_pos hc hfp,?_⟩
  have hh := Real.log_le_log hpos hf
  rw [Real.log_pow,Real.log_inv] at hh
  norm_num only [Nat.cast_ofNat] at hh
  rw [one_div,Real.log_inv,Real.log_mul hc.ne' hfp.ne',one_div,Real.log_inv]
  linarith

lemma deletion_cost_le_quarter (θ : ℝ) (_hθ : 0<θ) (D s : ℕ) (hs : 1 ≤ s)
    (hscale : 4*((D:ℝ)+1)≤θ*s) :
    (s^2+D*s^3:ℕ)≤θ/4*(s:ℝ)^4 := by
  have hspos : (0:ℝ)<s := Nat.cast_pos.mpr (by omega)
  have hs1 : (1:ℝ) ≤ s := by exact_mod_cast hs
  have h2 : (s:ℝ)^2≤(s:ℝ)^3 := by nlinarith [sq_nonneg (s:ℝ)]
  have hh := mul_le_mul_of_nonneg_right hscale (show 0≤(s:ℝ)^3 by positivity)
  push_cast
  nlinarith

lemma eventually_log_dominates (C B : ℝ) (_hC : 0≤C) :
    ∀ᶠ s : ℕ in atTop, C*(2*Real.log (Real.log s)+B)<Real.log s/4 := by
  have hl : Tendsto (fun s : ℕ => Real.log (s:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa only [pow_one,one_mul,add_zero] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hc : Tendsto (fun s : ℕ => B/Real.log s) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hl
  have ht : Tendsto (fun s : ℕ => C*(2*(Real.log (Real.log s)/Real.log s)+B/Real.log s))
      atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := C)).mul (((tendsto_const_nhds (x := (2:ℝ))).mul (hr.comp hl)).add hc)
    simpa only [Function.comp_apply,mul_zero,zero_add] using hh
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4)),
    hl.eventually (eventually_gt_atTop (0:ℝ))] with s hs hspos
  have he : C*(2*(Real.log (Real.log s)/Real.log s)+B/Real.log s) =
      C*(2*Real.log (Real.log s)+B)/Real.log s := by ring
  rw [he] at hs
  have hh := (div_lt_iff₀ hspos).mp hs
  linarith

end CriticalPercolation
end
end
end

end OAI
