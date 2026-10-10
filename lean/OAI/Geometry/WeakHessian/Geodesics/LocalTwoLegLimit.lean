import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.LocalizedScaling
import OAI.Geometry.WeakHessian.Geodesics.TwoLegLimit

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter
open scoped Topology

lemma vanishing_diffusion_local_two_leg {Z E A B C d s f L R a₀ : ℝ}
    {act err₀ err₁ : ℝ → ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) (hL : 0 ≤ L)
    (hact : Tendsto act (𝓝[>] 0) (𝓝 a₀))
    (herr₀ : Tendsto err₀ (𝓝[>] 0) (𝓝 0)) (herr₁ : Tendsto err₁ (𝓝[>] 0) (𝓝 0))
    (h : ∀ᶠ T : ℝ in 𝓝[>] 0,∃ M : ℝ,0 ≤ M ∧ M^2 ≤ A+B*T+16*T^2*d^2 ∧
      Z ≤ E*act T+err₀ T+err₁ T+T*(C+2*d*M)+s*(f+L*(2*M+R))) :
    Z ≤ E*a₀+s*(f+L*(2*Real.sqrt A+R)) := by
  have H : ∀ᶠ T : ℝ in 𝓝[>] 0,
      Z ≤ E*act T+err₀ T+err₁ T+T*(C+2*d*Real.sqrt (A+B*T+16*T^2*d^2))+
        s*(f+L*(2*Real.sqrt (A+B*T+16*T^2*d^2)+R)) := by
    filter_upwards [h,self_mem_nhdsWithin] with T hT hTp
    obtain ⟨M,hMn,hM,hZ⟩ := hT
    have hMs := Real.le_sqrt_of_sq_le hM
    apply hZ.trans
    have ht : 0 ≤ T := le_of_lt hTp
    gcongr
  have hmom := (show ContinuousAt (fun T : ℝ =>
      T*(C+2*d*Real.sqrt (A+B*T+16*T^2*d^2))+s*(f+L*(2*Real.sqrt (A+B*T+16*T^2*d^2)+R))) 0
    from by fun_prop).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hlim := ((((tendsto_const_nhds (x := E)).mul hact).add herr₀).add herr₁).add hmom
  have H' : ∀ᶠ T : ℝ in 𝓝[>] 0,
      Z ≤ E*act T+err₀ T+err₁ T+
        (T*(C+2*d*Real.sqrt (A+B*T+16*T^2*d^2))+s*(f+L*(2*Real.sqrt (A+B*T+16*T^2*d^2)+R))) := by
    filter_upwards [H] with T hT
    simpa only [add_assoc] using hT
  have HH := ge_of_tendsto hlim H'
  simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul,add_zero,zero_add] using HH

lemma midpoint_bound_of_local_two_leg_approx {D c CG CF L f₀ f₁ fz LD J : ℝ}
    (h : ∀ᶠ s : ℝ in 𝓝[>] 0,∀ᶠ r : ℝ in 𝓝[>] 0,∀ δ q : ℝ,0 < δ → 0 < q →
      D^2/4-LD*(r+δ*(D/2+2*r))-J*q ≤
        (D/2+2*r)^2*localActionLimit c CG s+
        s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r+δ*(D+4*r)))) :
    (f₀+f₁)/2-c/8*D^2 ≤ fz := by
  have Hs : ∀ᶠ s : ℝ in 𝓝[>] 0,
      D^2/4 ≤ (D/2)^2*localActionLimit c CG s+
        s*(2*fz-f₀-f₁+L*(2*Real.sqrt (16*s*CF))) := by
    filter_upwards [h] with s hs
    have Hr : ∀ᶠ r : ℝ in 𝓝[>] 0,
        D^2/4-LD*r ≤ (D/2+2*r)^2*localActionLimit c CG s+
          s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r)) := by
      filter_upwards [hs] with r hr
      have Hδ (δ : ℝ) (hδ : 0 < δ) :
          D^2/4-LD*(r+δ*(D/2+2*r)) ≤ (D/2+2*r)^2*localActionLimit c CG s+
            s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r+δ*(D+4*r))) := by
        have H := le_at_zero_of_positive
          (f := fun q => D^2/4-LD*(r+δ*(D/2+2*r))-J*q)
          (g := fun _ => (D/2+2*r)^2*localActionLimit c CG s+
            s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r+δ*(D+4*r))))
          (by fun_prop) continuousAt_const (fun q hq => hr δ q hδ hq)
        simpa only [mul_zero,sub_zero] using H
      have H := le_at_zero_of_positive
        (f := fun δ => D^2/4-LD*(r+δ*(D/2+2*r)))
        (g := fun δ => (D/2+2*r)^2*localActionLimit c CG s+
          s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r+δ*(D+4*r))))
        (by fun_prop) (by fun_prop) Hδ
      simpa only [zero_mul,add_zero] using H
    have H := le_of_tendsto_of_tendsto
      ((show ContinuousAt (fun r : ℝ => D^2/4-LD*r) 0 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds)
      ((show ContinuousAt (fun r : ℝ => (D/2+2*r)^2*localActionLimit c CG s+
        s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r))) 0 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds) Hr
    simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul,zero_add,add_zero,sub_zero] using H
  have Hq : ∀ᶠ s : ℝ in 𝓝[>] 0,
      0 ≤ D^2/4*((localActionLimit c CG s-1)/s)+(2*fz-f₀-f₁)+2*L*Real.sqrt (16*s*CF) := by
    filter_upwards [Hs,self_mem_nhdsWithin] with s hs hsp
    have hpos : 0 < s := hsp
    apply (mul_nonneg_iff_of_pos_left hpos).mp
    field_simp [hpos.ne']
    ring_nf at hs ⊢
    nlinarith only [hs]
  have hlim := localActionLimit_slope_limit c CG
  have hsqrt : Tendsto (fun s : ℝ => Real.sqrt (16*s*CF)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    convert (show ContinuousAt (fun s : ℝ => Real.sqrt (16*s*CF)) 0 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds using 1
    simp
  have HH := ge_of_tendsto
    ((((tendsto_const_nhds (x := D^2/4)).mul hlim).add
      (tendsto_const_nhds (x := 2*fz-f₀-f₁))).add ((tendsto_const_nhds (x := 2*L)).mul hsqrt)) Hq
  nlinarith [HH]
end WeakHessian

end
end

end OAI
