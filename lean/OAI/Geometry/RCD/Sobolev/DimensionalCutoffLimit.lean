import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # One-sided slopes from dimensional cutoff secants -/

open Set Filter
open scoped Topology
namespace RegularPointCoordinates

theorem frequent_right_slope_of_limiting_secants {D G e : ℝ → ℝ} {t c g : ℝ}
    (hc : 0 < c) (hG : Tendsto G atTop (𝓝 g)) (he : Tendsto e atTop (𝓝 0))
    (hsec : ∀ᶠ R : ℝ in atTop,
      (D (t+Real.exp (-c*R))-D t)/Real.exp (-c*R) ≤ G R+e R) :
    ∀ r, g < r → ∃ᶠ s in 𝓝[>] t, slope D t s < r := by
  intro r hr
  have hh := exp_neg_mul_tendsto_zero hc
  have ht : Tendsto (fun R : ℝ => t+Real.exp (-c*R)) atTop (𝓝 t) := by simpa using hh.const_add t
  have ht' : Tendsto (fun R : ℝ => t+Real.exp (-c*R)) atTop (𝓝[>] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall fun R => by
      exact lt_add_of_pos_right t (Real.exp_pos _)⟩
  have hlim : Tendsto (fun R => G R+e R) atTop (𝓝 g) := by simpa using hG.add he
  apply ht'.frequently
  apply Filter.Eventually.frequently
  filter_upwards [hsec,hlim.eventually (Iio_mem_nhds hr)] with R hs hl
  simpa only [slope_def_field,add_sub_cancel_left] using hs.trans_lt hl

theorem frequent_slope_of_dimensional_cutoffs {D Q G : ℝ → ℝ}
    {t b L C A H g : ℝ} (hb : 0 ≤ b) (hG : Tendsto G atTop (𝓝 g))
    (herr : ∀ᶠ R : ℝ in atTop,
      |Q R-D (t+Real.exp (-(b+1)*R))| ≤ L*Real.exp (-(2*b+4)*R) ∧
      (Q R-D t)/(2*Real.exp (-(b+1)*R)) ≤ G R+
        (C*Real.exp (b*R))*(A*Real.exp (-(b+1)*R)+
          ((Real.exp (-(b+1)*R))⁻¹+2)*(H*Real.exp (-(2*b+4)*R)))) :
    ∀ r, g < r → ∃ᶠ s in 𝓝[>] t, slope (fun v => D v/2) t s < r := by
  have he := diagonal_polynomial_exponential_error hb 0 L 0 C A H
  simp only [zero_mul,zero_add] at he
  apply frequent_right_slope_of_limiting_secants (c := b+1) (by linarith) hG he
  filter_upwards [herr] with R hR
  have hh : 0 < Real.exp (-(b+1)*R) := Real.exp_pos _
  have hx : D (t+Real.exp (-(b+1)*R))-Q R ≤ L*Real.exp (-(2*b+4)*R) := by
    linarith [(abs_le.mp hR.1).1]
  have hs := div_le_div_of_nonneg_right hx (show 0 ≤ 2*Real.exp (-(b+1)*R) by positivity)
  have hbase := hR.2
  calc
    (D (t+Real.exp (-(b+1)*R))/2-D t/2)/Real.exp (-(b+1)*R) =
        (Q R-D t)/(2*Real.exp (-(b+1)*R))+
        (D (t+Real.exp (-(b+1)*R))-Q R)/(2*Real.exp (-(b+1)*R)) := by ring
    _ ≤ (G R+(C*Real.exp (b*R))*(A*Real.exp (-(b+1)*R)+
          ((Real.exp (-(b+1)*R))⁻¹+2)*(H*Real.exp (-(2*b+4)*R))))+
        L*Real.exp (-(2*b+4)*R)/(2*Real.exp (-(b+1)*R)) := add_le_add hbase hs
    _ = _ := by ring

end RegularPointCoordinates

end OAI
