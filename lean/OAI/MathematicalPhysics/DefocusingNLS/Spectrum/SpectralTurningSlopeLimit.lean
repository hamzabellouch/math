import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleFrequencyJet
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningScaleLimit

namespace OAI

/-! The derivative of the frequency has the Airy normalization at every
fixed rescaled point, uniformly in the angular parameter. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralTurning_scaled_slope_bound (eta r₀ d xi : ℝ)
    (hr₀ : 0 < r₀) (hd : 0 ≤ d) (heta : 0 ≤ eta) (hr : r₀+d*xi ≠ 0)
    (hscale : spectralLiouvilleSlope eta r₀*d^3 = 1) :
    |spectralLiouvilleSlope eta (r₀+d*xi)*d^3-1| ≤
      |d*xi/r₀|+|(r₀/(r₀+d*xi))^3-1| := by
  let A := r₀/8*d^3
  let B := 2*(eta+99/4)/r₀^3*d^3
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hAB : A+B = 1 := by
    dsimp only [A,B]
    simpa only [spectralLiouvilleSlope,add_mul] using hscale
  have hA1 : A ≤ 1 := by linarith
  have hB1 : B ≤ 1 := by linarith
  have he : spectralLiouvilleSlope eta (r₀+d*xi)*d^3-1 =
      A*(d*xi/r₀)+B*((r₀/(r₀+d*xi))^3-1) := by
    calc
      _ = spectralLiouvilleSlope eta (r₀+d*xi)*d^3-(A+B) := by rw [hAB]
      _ = _ := by
        dsimp only [spectralLiouvilleSlope,A,B]
        field_simp [hr₀.ne',hr]
        ring_nf
  rw [he]
  calc
    _ ≤ |A*(d*xi/r₀)|+|B*((r₀/(r₀+d*xi))^3-1)| := abs_add_le _ _
    _ = A*|d*xi/r₀|+B*|(r₀/(r₀+d*xi))^3-1| := by
      rw [abs_mul A (d*xi/r₀),abs_mul B ((r₀/(r₀+d*xi))^3-1),
        abs_of_nonneg hA,abs_of_nonneg hB]
    _ ≤ _ := add_le_add (mul_le_of_le_one_left (abs_nonneg _) hA1)
      (mul_le_of_le_one_left (abs_nonneg _) hB1)

theorem spectralTurning_scaled_slope_tendsto (eta r₀ d : ℕ → ℝ) (xi : ℝ)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧
      spectralLiouvilleSlope (eta n) (r₀ n)*(d n)^3 = 1) :
    Tendsto (fun n => spectralLiouvilleSlope (eta n) (r₀ n+d n*xi)*(d n)^3)
      atTop (𝓝 1) := by
  have hd := spectralTurningScale_tendsto eta r₀ d hr₀ hdata
  let t := fun n => d n*xi/r₀ n
  have ht : Tendsto t atTop (𝓝 0) := by
    convert (hd.mul (tendsto_inv_atTop_zero.comp hr₀)).mul_const xi using 1
    · funext n
      dsimp only [t,Function.comp_def]
      ring_nf
    · simp only [mul_zero,zero_mul]
  have ht1 : Tendsto (fun n => 1+t n) atTop (𝓝 1) := by
    simpa only [add_zero] using ht.const_add 1
  have hrec : Tendsto (fun n => ((1+t n)⁻¹)^3-1) atTop (𝓝 0) := by
    simpa only [inv_one,one_pow,sub_self] using ((ht1.inv₀ (by norm_num)).pow 3).sub_const 1
  have hrate : Tendsto (fun n => |t n|+|((1+t n)⁻¹)^3-1|) atTop (𝓝 0) := by
    simpa only [abs_zero,zero_add] using ht.abs.add hrec.abs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) _ hrate
  filter_upwards [hdata,ht1.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn htpos
  have hr : r₀ n+d n*xi ≠ 0 := by
    have he : r₀ n+d n*xi = r₀ n*(1+t n) := by
      dsimp only [t]
      field_simp [hn.1.ne']
    rw [he]
    exact mul_ne_zero hn.1.ne' htpos.ne'
  have hbound := spectralTurning_scaled_slope_bound (eta n) (r₀ n) (d n) xi
    hn.1 hn.2.1 hn.2.2.1 hr hn.2.2.2
  have he : r₀ n/(r₀ n+d n*xi) = (1+t n)⁻¹ := by
    dsimp only [t]
    field_simp [hn.1.ne',hr]
  simpa only [Real.norm_eq_abs,he,t] using hbound

end DefocusingNLS

end OAI
