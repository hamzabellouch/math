import OAI.NumberTheory.CubicMoment.Estimates.MellinContour
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! The pole crossed by the Type-I Mellin contour. These are calculus
lemmas: no analytic continuation or arithmetic estimate is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace CubicFirstMoment

lemma simplePole_line_continuous {c : ℝ} (hc : c ≠ 0) :
    Continuous (fun t : ℝ => ((c:ℂ)+(t:ℂ)*Complex.I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro t h
  apply hc
  have hre := congrArg Complex.re h
  simpa using hre

/-- The symmetric integral of a simple-pole kernel is an arctangent.
Keeping its imaginary part exact avoids any conditionally convergent
integral in the eventual contour shift. -/
lemma simplePole_line_integral {c : ℝ} (hc : c ≠ 0) (T : ℝ) :
    (∫ t in -T..T, ((c:ℂ)+(t:ℂ)*Complex.I)⁻¹) = (2*Real.arctan (T/c):ℝ) := by
  have hi : IntervalIntegrable (fun t : ℝ => ((c:ℂ)+(t:ℂ)*Complex.I)⁻¹)
      volume (-T) T := (simplePole_line_continuous hc).intervalIntegrable (-T) T
  have hre (t : ℝ) : (((c:ℂ)+(t:ℂ)*Complex.I)⁻¹).re = c/(c^2+t^2) := by
    simp [Complex.inv_re,Complex.normSq_apply,pow_two]
  have him (t : ℝ) : (((c:ℂ)+(t:ℂ)*Complex.I)⁻¹).im = -(t/(c^2+t^2)) := by
    simp [Complex.inv_im,Complex.normSq_apply,pow_two]
    ring
  apply Complex.ext
  · change RCLike.re (∫ t in -T..T, ((c:ℂ)+(t:ℂ)*Complex.I)⁻¹) = _
    rw [← intervalIntegral.intervalIntegral_re hi]
    change (∫ t in -T..T, (((c:ℂ)+(t:ℂ)*Complex.I)⁻¹).re) = 2*Real.arctan (T/c)
    simp_rw [hre]
    rw [integral_div_sq_add_sq]
    simp [neg_div,Real.arctan_neg,two_mul]
  · change RCLike.im (∫ t in -T..T, ((c:ℂ)+(t:ℂ)*Complex.I)⁻¹) = _
    rw [← intervalIntegral.intervalIntegral_im hi]
    change (∫ t in -T..T, (((c:ℂ)+(t:ℂ)*Complex.I)⁻¹).im) = 0
    simp_rw [him]
    rw [intervalIntegral.integral_neg,integral_id_div_sq_add_sq hc]
    simp

lemma simplePole_line_tendsto_pos {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T : ℝ => ∫ t in -T..T, ((c:ℂ)+(t:ℂ)*Complex.I)⁻¹)
      atTop (𝓝 (Real.pi:ℂ)) := by
  simp_rw [simplePole_line_integral hc.ne']
  have h := ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
    (tendsto_id.atTop_div_const hc)).const_mul 2
  rw [show 2*(Real.pi/2) = Real.pi by ring] at h
  simpa only [Function.comp_def,id_eq,Complex.ofReal_mul,Complex.ofReal_ofNat] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp h

lemma simplePole_line_tendsto_neg {c : ℝ} (hc : c < 0) :
    Tendsto (fun T : ℝ => ∫ t in -T..T, ((c:ℂ)+(t:ℂ)*Complex.I)⁻¹)
      atTop (𝓝 (-(Real.pi:ℂ))) := by
  simp_rw [simplePole_line_integral hc.ne]
  have h := ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp
    (tendsto_id.atTop_div_const_of_neg hc)).const_mul 2
  rw [show 2*(-(Real.pi/2)) = -Real.pi by ring] at h
  simpa only [Function.comp_def,id_eq,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_neg] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp h

def poleRegularPart (M g : ℂ → ℂ) (ρ c : ℂ) (s : ℂ) : ℂ :=
  M s*g s+ρ*dslope M c s

lemma poleRegularPart_differentiableOn (M g : ℂ → ℂ) (ρ c : ℂ)
    (hM : Differentiable ℂ M) {a b : ℝ}
    (hg : DifferentiableOn ℂ g (closedVerticalStrip a b)) :
    DifferentiableOn ℂ (poleRegularPart M g ρ c) (closedVerticalStrip a b) := by
  have hd : Differentiable ℂ (dslope M c) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr
      hM.differentiableOn
  exact (hM.differentiableOn.mul hg).add (hd.differentiableOn.const_mul ρ)

lemma poleRegularPart_eq (M g : ℂ → ℂ) (ρ c s : ℂ) (hs : s ≠ c) :
    poleRegularPart M g ρ c s =
      M s*(g s+ρ/(s-c))-(ρ*M c)*(s-c)⁻¹ := by
  rw [poleRegularPart,dslope_of_ne M hs,slope_def_field]
  ring

/-- The horizontal edges of the subtracted constant pole tend to zero. -/
lemma simplePole_horizontal_tendsto (a b c : ℝ) :
    Tendsto (fun T : ℝ => ∫ x in a..b,
      ((x:ℂ)+(T:ℂ)*Complex.I-(c:ℂ))⁻¹) atTop (𝓝 0) := by
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖∫ x in a..b, ((x:ℂ)+(T:ℂ)*Complex.I-(c:ℂ))⁻¹‖ ≤ T⁻¹*|b-a| := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x _
    rw [norm_inv]
    apply inv_anti₀ (by linarith : 0 < T)
    have h := Complex.abs_im_le_norm ((x:ℂ)+(T:ℂ)*Complex.I-(c:ℂ))
    simpa [abs_of_nonneg (show 0 ≤ T by linarith)] using h
  exact squeeze_zero_norm' hbound (by simpa using
    (tendsto_inv_atTop_zero.mul_const |b-a|))

private lemma poleRegularPart_vertical_limit (M g : ℂ → ℂ) (ρ : ℂ) (c σ : ℝ)
    (hσ : σ ≠ c)
    (hf : Integrable (fun t : ℝ => M ((σ:ℂ)+(t:ℂ)*Complex.I)*
      (g ((σ:ℂ)+(t:ℂ)*Complex.I)+ρ/((σ:ℂ)+(t:ℂ)*Complex.I-(c:ℂ)))))
    {L : ℂ} (hL : Tendsto (fun T : ℝ => ∫ t in -T..T,
      (((σ-c:ℝ):ℂ)+(t:ℂ)*Complex.I)⁻¹) atTop (𝓝 L)) :
    Tendsto (fun T : ℝ => ∫ t in -T..T,
      poleRegularPart M g ρ c ((σ:ℂ)+(t:ℂ)*Complex.I)) atTop
      (𝓝 ((∫ t : ℝ, M ((σ:ℂ)+(t:ℂ)*Complex.I)*
        (g ((σ:ℂ)+(t:ℂ)*Complex.I)+ρ/((σ:ℂ)+(t:ℂ)*Complex.I-(c:ℂ))))-
          (ρ*M c)*L)) := by
  have hne (t : ℝ) : (σ:ℂ)+(t:ℂ)*Complex.I ≠ (c:ℂ) := by
    intro h
    exact hσ (by simpa using congrArg Complex.re h)
  have he (T : ℝ) : (∫ t in -T..T,
      poleRegularPart M g ρ c ((σ:ℂ)+(t:ℂ)*Complex.I)) =
      (∫ t in -T..T, M ((σ:ℂ)+(t:ℂ)*Complex.I)*
        (g ((σ:ℂ)+(t:ℂ)*Complex.I)+ρ/((σ:ℂ)+(t:ℂ)*Complex.I-(c:ℂ))))-
          (ρ*M c)*(∫ t in -T..T, (((σ-c:ℝ):ℂ)+(t:ℂ)*Complex.I)⁻¹) := by
    simp_rw [poleRegularPart_eq M g ρ c _ (hne _)]
    have hc : Continuous (fun t : ℝ => (((σ-c:ℝ):ℂ)+(t:ℂ)*Complex.I)⁻¹) :=
      simplePole_line_continuous (sub_ne_zero.mpr hσ)
    have heq (t : ℝ) : ((σ:ℂ)+(t:ℂ)*Complex.I-(c:ℂ))⁻¹ =
        (((σ-c:ℝ):ℂ)+(t:ℂ)*Complex.I)⁻¹ := by
      congr 1
      push_cast
      ring
    simp_rw [heq]
    rw [intervalIntegral.integral_sub hf.intervalIntegrable
      ((hc.const_mul _).intervalIntegrable _ _),intervalIntegral.integral_const_mul]
  simp_rw [he]
  exact (intervalIntegral_tendsto_integral hf tendsto_neg_atTop_atBot tendsto_id).sub
    (hL.const_mul (ρ*M c))

/-- A one-pole contour shift with both horizontal limits kept explicit.
The removable part is constructed from a divided difference, and the
residue contribution comes from the proved arctangent kernel limits. -/
theorem mellin_single_pole_shift (M g : ℂ → ℂ) (ρ : ℂ) {a b c : ℝ}
    (hac : a < c) (hcb : c < b) (hM : Differentiable ℂ M)
    (hg : DifferentiableOn ℂ g (closedVerticalStrip a b))
    (ha : Integrable (fun t : ℝ => M ((a:ℂ)+(t:ℂ)*Complex.I)*
      (g ((a:ℂ)+(t:ℂ)*Complex.I)+ρ/((a:ℂ)+(t:ℂ)*Complex.I-(c:ℂ)))))
    (hb : Integrable (fun t : ℝ => M ((b:ℂ)+(t:ℂ)*Complex.I)*
      (g ((b:ℂ)+(t:ℂ)*Complex.I)+ρ/((b:ℂ)+(t:ℂ)*Complex.I-(c:ℂ)))))
    (hTop : Tendsto (fun T : ℝ => ∫ x in a..b,
      poleRegularPart M g ρ c ((x:ℂ)+(T:ℂ)*Complex.I)) atTop (𝓝 0))
    (hBot : Tendsto (fun T : ℝ => ∫ x in a..b,
      poleRegularPart M g ρ c ((x:ℂ)-(T:ℂ)*Complex.I)) atTop (𝓝 0)) :
    (∫ t : ℝ, M ((b:ℂ)+(t:ℂ)*Complex.I)*
      (g ((b:ℂ)+(t:ℂ)*Complex.I)+ρ/((b:ℂ)+(t:ℂ)*Complex.I-(c:ℂ)))) =
    (∫ t : ℝ, M ((a:ℂ)+(t:ℂ)*Complex.I)*
      (g ((a:ℂ)+(t:ℂ)*Complex.I)+ρ/((a:ℂ)+(t:ℂ)*Complex.I-(c:ℂ))))+
        (2*Real.pi:ℝ)*(ρ*M c) := by
  let Ia := ∫ t : ℝ, M ((a:ℂ)+(t:ℂ)*Complex.I)*
    (g ((a:ℂ)+(t:ℂ)*Complex.I)+ρ/((a:ℂ)+(t:ℂ)*Complex.I-(c:ℂ)))
  let Ib := ∫ t : ℝ, M ((b:ℂ)+(t:ℂ)*Complex.I)*
    (g ((b:ℂ)+(t:ℂ)*Complex.I)+ρ/((b:ℂ)+(t:ℂ)*Complex.I-(c:ℂ)))
  have hla := poleRegularPart_vertical_limit M g ρ c a hac.ne ha
    (simplePole_line_tendsto_neg (sub_neg.mpr hac))
  have hlb := poleRegularPart_vertical_limit M g ρ c b hcb.ne' hb
    (simplePole_line_tendsto_pos (sub_pos.mpr hcb))
  have hlim := ((hBot.sub hTop).add (hlb.const_mul Complex.I)).sub
    (hla.const_mul Complex.I)
  have hz : (0:ℂ)-0+Complex.I*(Ib-(ρ*M c)*Real.pi)-
      Complex.I*(Ia-(ρ*M c)*(-Real.pi)) = 0 := by
    apply tendsto_nhds_unique hlim
    apply tendsto_const_nhds.congr'
    exact Filter.Eventually.of_forall (fun T =>
      (mellin_rectangle_identity (hac.trans hcb).le (poleRegularPart M g ρ c)
        (poleRegularPart_differentiableOn M g ρ c hM hg) T).symm)
  have he : Ib-(ρ*M c)*Real.pi = Ia-(ρ*M c)*(-Real.pi) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination hz
  change Ib = Ia+((2*Real.pi:ℝ):ℂ)*(ρ*M c)
  push_cast
  linear_combination he

lemma poleRegularPart_edge_bound (M g : ℂ → ℂ) (ρ : ℂ) {a b c T : ℝ}
    (hab : a ≤ b) (hT : 1 ≤ |T|) (H : ℝ → ℝ)
    (hH : ∀ x ∈ Icc a b,
      ‖M ((x:ℂ)+(T:ℂ)*Complex.I)*
        (g ((x:ℂ)+(T:ℂ)*Complex.I)+ρ/((x:ℂ)+(T:ℂ)*Complex.I-(c:ℂ)))‖ ≤ H T) :
    ‖∫ x in a..b, poleRegularPart M g ρ c ((x:ℂ)+(T:ℂ)*Complex.I)‖ ≤
      (H T+‖ρ*M c‖/|T|)*|b-a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hx' : x ∈ Icc a b := by
    rw [uIoc_of_le hab] at hx
    exact ⟨hx.1.le,hx.2⟩
  have hTp : 0 < |T| := zero_lt_one.trans_le hT
  have hne : (x:ℂ)+(T:ℂ)*Complex.I ≠ (c:ℂ) := by
    intro he
    have him := congrArg Complex.im he
    have : T = 0 := by simpa using him
    simp [this] at hTp
  have hn : |T| ≤ ‖(x:ℂ)+(T:ℂ)*Complex.I-(c:ℂ)‖ := by
    simpa using Complex.abs_im_le_norm ((x:ℂ)+(T:ℂ)*Complex.I-(c:ℂ))
  rw [poleRegularPart_eq M g ρ c _ hne]
  calc
    _ ≤ ‖M ((x:ℂ)+(T:ℂ)*Complex.I)*
        (g ((x:ℂ)+(T:ℂ)*Complex.I)+ρ/((x:ℂ)+(T:ℂ)*Complex.I-(c:ℂ)))‖+
        ‖(ρ*M c)*((x:ℂ)+(T:ℂ)*Complex.I-(c:ℂ))⁻¹‖ := norm_sub_le _ _
    _ ≤ H T+‖ρ*M c‖/|T| := by
      apply add_le_add (hH x hx')
      rw [norm_mul,norm_inv,div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hTp hn) (_root_.norm_nonneg _)

/-- A vanishing majorant for the original meromorphic integrand supplies
the regularized horizontal limits required by the residue calculation. -/
theorem mellin_single_pole_shift_of_majorant (M g : ℂ → ℂ) (ρ : ℂ) {a b c : ℝ}
    (hac : a < c) (hcb : c < b) (hM : Differentiable ℂ M)
    (hg : DifferentiableOn ℂ g (closedVerticalStrip a b))
    (ha : Integrable (fun t : ℝ => M ((a:ℂ)+(t:ℂ)*Complex.I)*
      (g ((a:ℂ)+(t:ℂ)*Complex.I)+ρ/((a:ℂ)+(t:ℂ)*Complex.I-(c:ℂ)))))
    (hb : Integrable (fun t : ℝ => M ((b:ℂ)+(t:ℂ)*Complex.I)*
      (g ((b:ℂ)+(t:ℂ)*Complex.I)+ρ/((b:ℂ)+(t:ℂ)*Complex.I-(c:ℂ)))))
    (H : ℝ → ℝ) (hHt : Tendsto H atTop (𝓝 0)) (hHb : Tendsto H atBot (𝓝 0))
    (hH : ∀ x ∈ Icc a b, ∀ t : ℝ, 1 ≤ |t| →
      ‖M ((x:ℂ)+(t:ℂ)*Complex.I)*
        (g ((x:ℂ)+(t:ℂ)*Complex.I)+ρ/((x:ℂ)+(t:ℂ)*Complex.I-(c:ℂ)))‖ ≤ H t) :
    (∫ t : ℝ, M ((b:ℂ)+(t:ℂ)*Complex.I)*
      (g ((b:ℂ)+(t:ℂ)*Complex.I)+ρ/((b:ℂ)+(t:ℂ)*Complex.I-(c:ℂ)))) =
    (∫ t : ℝ, M ((a:ℂ)+(t:ℂ)*Complex.I)*
      (g ((a:ℂ)+(t:ℂ)*Complex.I)+ρ/((a:ℂ)+(t:ℂ)*Complex.I-(c:ℂ))))+
        (2*Real.pi:ℝ)*(ρ*M c) := by
  apply mellin_single_pole_shift M g ρ hac hcb hM hg ha hb
  · apply squeeze_zero_norm'
      (a := fun T : ℝ => (H T+‖ρ*M c‖*T⁻¹)*|b-a|)
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
      simpa only [abs_of_nonneg (show 0 ≤ T by linarith),div_eq_mul_inv] using
        poleRegularPart_edge_bound M g ρ (hac.trans hcb).le
          (show 1 ≤ |T| by simpa [abs_of_nonneg (show 0 ≤ T by linarith)] using hT) H
          (fun x hx => hH x hx T (by simpa [abs_of_nonneg (show 0 ≤ T by linarith)] using hT))
    · simpa using (hHt.add (tendsto_inv_atTop_zero.const_mul ‖ρ*M c‖)).mul_const |b-a|
  · apply squeeze_zero_norm'
      (a := fun T : ℝ => (H (-T)+‖ρ*M c‖*T⁻¹)*|b-a|)
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
      have ht : 1 ≤ |-T| := by simpa [abs_neg,abs_of_nonneg (show 0 ≤ T by linarith)] using hT
      simpa only [Complex.ofReal_neg,neg_mul,sub_eq_add_neg,abs_neg,
        abs_of_nonneg (show 0 ≤ T by linarith),div_eq_mul_inv] using
          poleRegularPart_edge_bound M g ρ (hac.trans hcb).le ht H (fun x hx => hH x hx (-T) ht)
    · simpa using ((hHb.comp tendsto_neg_atTop_atBot).add
        (tendsto_inv_atTop_zero.const_mul ‖ρ*M c‖)).mul_const |b-a|

end CubicFirstMoment

end

end OAI
