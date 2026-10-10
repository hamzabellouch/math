import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter
open scoped Topology

lemma le_at_zero_of_positive {f g : ℝ → ℝ} (hf : ContinuousAt f 0)
    (hg : ContinuousAt g 0) (h : ∀ t,0 < t → f t ≤ g t) : f 0 ≤ g 0 := by
  exact le_of_tendsto_of_tendsto (hf.tendsto.mono_left nhdsWithin_le_nhds)
    (hg.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun t (ht : t ∈ Ioi (0:ℝ)) => h t ht)

lemma vanishing_diffusion_two_leg {Z E K G s A B C c f L R : ℝ}
    (hs : 0 ≤ s) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (h : ∀ T : ℝ,0 < T → ∃ M : ℝ,0 ≤ M ∧ M^2 ≤ A+B*T+16*T^2*c^2 ∧
      Z ≤ E*Real.exp (2*(K*T+G*s))+2*T*(C+2*c*M)+2*s*(f+L*(2*M+R))) :
    Z ≤ E*Real.exp (2*G*s)+2*s*(f+L*(2*Real.sqrt A+R)) := by
  have H (T : ℝ) (hT : 0 < T) :
      Z ≤ E*Real.exp (2*(K*T+G*s))+2*T*(C+2*c*Real.sqrt (A+B*T+16*T^2*c^2))+
        2*s*(f+L*(2*Real.sqrt (A+B*T+16*T^2*c^2)+R)) := by
    obtain ⟨M,hMn,hM,hZ⟩ := h T hT
    have hMs := Real.le_sqrt_of_sq_le hM
    apply hZ.trans
    gcongr
  have H0 := le_at_zero_of_positive (f := fun _ => Z) (g := fun T =>
    E*Real.exp (2*(K*T+G*s))+2*T*(C+2*c*Real.sqrt (A+B*T+16*T^2*c^2))+
      2*s*(f+L*(2*Real.sqrt (A+B*T+16*T^2*c^2)+R)))
    continuousAt_const (by fun_prop) H
  simpa only [mul_zero,add_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul,zero_add,mul_assoc] using H0

lemma midpoint_bound_of_two_leg_approx {D CG CF L f₀ f₁ fz : ℝ}
    (hD : 0 ≤ D) (hL : 0 ≤ L)
    (h : ∀ r δ s : ℝ,0 < r → 0 < δ → 0 < s →
      (max 0 (D-2*r-δ*(D+4*r)))^2/2 ≤
        2*(D/2+2*r)^2*Real.exp (2*CG*s)+
        2*s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r+δ*(D+4*r)))) :
    (f₀+f₁)/2-CG/4*D^2 ≤ fz := by
  lift L to ℝ≥0 using hL
  have Hr (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
      (max 0 (D-2*r))^2/2 ≤ 2*(D/2+2*r)^2*Real.exp (2*CG*s)+
        2*s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r)) := by
    have H := le_at_zero_of_positive
      (f := fun δ => (max 0 (D-2*r-δ*(D+4*r)))^2/2)
      (g := fun δ => 2*(D/2+2*r)^2*Real.exp (2*CG*s)+
        2*s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r+δ*(D+4*r))))
      (by fun_prop) (by fun_prop) (fun δ hδ => h r δ s hr hδ hs)
    simpa only [zero_mul,sub_zero,add_zero] using H
  have Hs (s : ℝ) (hs : 0 < s) :
      D^2/2 ≤ 2*(D/2)^2*Real.exp (2*CG*s)+
        2*s*(2*fz-f₀-f₁+L*(2*Real.sqrt (16*s*CF))) := by
    have H := le_at_zero_of_positive
      (f := fun r => (max 0 (D-2*r))^2/2)
      (g := fun r => 2*(D/2+2*r)^2*Real.exp (2*CG*s)+
        2*s*(2*fz-f₀-f₁+L*(2*Real.sqrt (4*r^2+16*s*CF)+2*r)))
      (by fun_prop) (by fun_prop) (fun r hr => Hr r s hr hs)
    simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul,zero_add,
      add_zero,sub_zero,max_eq_right hD] using H
  have Hq (s : ℝ) (hs : 0 < s) :
      0 ≤ D^2/4*((Real.exp (2*CG*s)-1)/s)+(2*fz-f₀-f₁)+2*L*Real.sqrt (16*s*CF) := by
    have H := Hs s hs
    apply (mul_nonneg_iff_of_pos_left hs).mp
    have hz : s ≠ 0 := hs.ne'
    field_simp
    ring_nf at H ⊢
    nlinarith only [H]
  have he : HasDerivAt (fun s : ℝ => Real.exp (2*CG*s)) (2*CG) 0 := by
    convert ((hasDerivAt_id (0:ℝ)).const_mul (2*CG)).exp using 1 <;> simp
  have hlim : Tendsto (fun s : ℝ => (Real.exp (2*CG*s)-1)/s) (𝓝[>] (0:ℝ)) (𝓝 (2*CG)) := by
    have H := he.tendsto_slope_zero_right
    simpa [smul_eq_mul,div_eq_mul_inv,mul_comm] using H
  have hsqrt : Tendsto (fun s : ℝ => Real.sqrt (16*s*CF)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    convert (show ContinuousAt (fun s : ℝ => Real.sqrt (16*s*CF)) 0 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds using 1
    simp
  have HH := ge_of_tendsto
    ((((tendsto_const_nhds (x := D^2/4)).mul hlim).add
      (tendsto_const_nhds (x := 2*fz-f₀-f₁))).add ((tendsto_const_nhds (x := 2*(L : ℝ))).mul hsqrt))
    (eventually_nhdsWithin_of_forall fun s (hs : s ∈ Ioi (0:ℝ)) => Hq s hs)
  nlinarith only [HH]
end WeakHessian

end
end

end OAI
