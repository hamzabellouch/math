import Mathlib
import OAI.Probability.SKSupport.Parabolic.ForwardGeometry

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.Heat

def heatKernel (t x : ℝ) := gaussianPDFReal 0 (Real.toNNReal t) x

lemma heatKernel_formula {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    heatKernel t x=(Real.sqrt (2*Real.pi*t))⁻¹*Real.exp (-x^2/(2*t)) := by
  simp only [heatKernel,gaussianPDFReal,Real.coe_toNNReal _ ht,sub_zero]

lemma heatKernel_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < heatKernel t x :=
  gaussianPDFReal_pos 0 _ x (ne_of_gt (Real.toNNReal_pos.mpr ht))

lemma varianceHeat_kernel {g : ℝ → ℝ} (hg : Measurable g) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    varianceHeat t g x=∫ y, heatKernel t (y-x)*g y := by
  rw [varianceHeat_eq_semigroup_toNNReal hg]
  unfold semigroup
  rw [integral_gaussianReal_eq_integral_smul (ne_of_gt (Real.toNNReal_pos.mpr ht))]
  rw [← integral_add_left_eq_self (fun y => heatKernel t (y-x)*g y) x]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [heatKernel,smul_eq_mul,add_sub_cancel_left]

lemma heatKernel_complete_square {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (x y : ℝ) :
    heatKernel t (y-x)*Real.exp (-y^2/(2*a)) =
      Real.sqrt (a/(a+t))*Real.exp (-x^2/(2*(a+t)))*
        heatKernel (a*t/(a+t)) (y-a/(a+t)*x) := by
  have hs := add_pos ha ht
  have hv : 0 < a*t/(a+t) := div_pos (mul_pos ha ht) hs
  have hscale : 0 < a/(a+t) := div_pos ha hs
  have he : -(y-x)^2/(2*t)+ -y^2/(2*a)=
      -x^2/(2*(a+t))+ -(y-a/(a+t)*x)^2/(2*(a*t/(a+t))) := by
    field_simp [ne_of_gt ha,ne_of_gt ht,ne_of_gt hs]
    ring
  have hroot : Real.sqrt (2*Real.pi*(a*t/(a+t))) =
      Real.sqrt (a/(a+t))*Real.sqrt (2*Real.pi*t) := by
    rw [← Real.sqrt_mul hscale.le]
    congr 1
    ring
  have hn : (Real.sqrt (2*Real.pi*t))⁻¹ =
      Real.sqrt (a/(a+t))*(Real.sqrt (2*Real.pi*(a*t/(a+t))))⁻¹ := by
    rw [hroot,mul_inv_rev]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hscale)]
  rw [heatKernel_formula ht.le,heatKernel_formula hv.le]
  rw [mul_assoc,← Real.exp_add,he,Real.exp_add,hn]
  ring

lemma varianceHeat_gaussian_weight {L : ℝ → ℝ} (hL : Measurable L)
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (x : ℝ) :
    varianceHeat t (fun y => Real.exp (-y^2/(2*a)+L y)) x =
      Real.sqrt (a/(a+t))*Real.exp (-x^2/(2*(a+t)))*
        varianceHeat (a*t/(a+t)) (fun y => Real.exp (L y)) (a/(a+t)*x) := by
  have hm : Measurable (fun y : ℝ => Real.exp (-y^2/(2*a)+L y)) := by fun_prop
  rw [varianceHeat_kernel hm ht,varianceHeat_kernel hL.exp (div_pos (mul_pos ha ht) (add_pos ha ht))]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Real.exp_add,← mul_assoc,heatKernel_complete_square ha ht]
  ring

lemma exp_varianceLogHeat_one {L : ℝ → ℝ} {K : ℝ≥0} (hL : LipschitzWith K L) (t x : ℝ) :
    Real.exp (varianceLogHeat 1 t L x)=varianceHeat t (fun y => Real.exp (L y)) x := by
  simp only [varianceLogHeat,one_ne_zero,ite_false,div_one,one_mul]
  exact Real.exp_log (by simpa only [one_mul] using varianceHeat_exp_pos hL 1 t x)

lemma exp_half_log {x : ℝ} (hx : 0 < x) : Real.exp ((1/2:ℝ)*Real.log x)=Real.sqrt x := by
  apply (sq_eq_sq₀ (Real.exp_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hx.le,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*((1/2)*Real.log x)=Real.log x by ring,Real.exp_log hx]

lemma varianceHeat_gaussian_forwardCorrection {L : ℝ → ℝ} {K : ℝ≥0}
    (hL : LipschitzWith K L) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (x : ℝ) :
    varianceHeat t (fun y => Real.exp (-y^2/(2*a)+L y)) x =
      Real.exp (-x^2/(2*(a+t))+forwardCorrection a L t x) := by
  rw [varianceHeat_gaussian_weight hL.continuous.measurable ha ht]
  simp only [forwardCorrection,forwardVariance,forwardScale,forwardTime,max_eq_left ht.le]
  rw [Real.exp_add,Real.exp_add,exp_varianceLogHeat_one hL,exp_half_log (div_pos ha (add_pos ha ht))]
  ring

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma heatKernel_uniform_lower {δ h x y : ℝ} (hδ : 0 < δ) (hδh : δ ≤ h) (hh : h ≤ 1)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-2/δ) ≤ heatKernel h (y-x) := by
  have hh0 := hδ.trans_le hδh
  have hz : |y-x| ≤ 2 := (abs_sub y x).trans (by linarith)
  have hz2 : (y-x)^2 ≤ 4 := by
    have hh := (sq_le_sq₀ (abs_nonneg (y-x)) (show (0:ℝ) ≤ 2 by norm_num)).mpr hz
    simpa only [sq_abs,show (2:ℝ)^2=4 by norm_num] using hh
  rw [heatKernel_formula hh0.le]
  apply mul_le_mul
  · apply inv_anti₀ (by positivity)
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_pos]
  · apply Real.exp_le_exp.mpr
    have hq : (y-x)^2/(2*h) ≤ 2/δ := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2*h) hδ).mpr
      nlinarith
    simpa only [neg_div] using neg_le_neg hq
  · positivity
  · positivity

lemma integrable_weighted_heatKernel {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : BoundedSmooth g) (c : ℝ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    Integrable (fun y => heatKernel h (y-x)*(g y*Real.exp (c*f y))) := by
  obtain ⟨G,hG⟩ := hg.bound
  have hi := integrable_weight_exp_translate hf hg.smooth.continuous.measurable hG c (Real.toNNReal h) x
  rw [gaussianReal_of_var_ne_zero _ (ne_of_gt (Real.toNNReal_pos.mpr hh))] at hi
  have hj := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 (Real.toNNReal h))
    (Eventually.of_forall (fun y => gaussianPDF_lt_top))).mp hi
  simp only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul] at hj
  have hk := hj.comp_add_left (-x)
  apply hk.congr
  filter_upwards [] with y
  simp only [← add_assoc,add_neg_cancel,zero_add]
  rw [show -x+y=y-x by ring]
  rfl

lemma varianceHeat_exp_eq_exp_log {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (c h x : ℝ) : varianceHeat h (fun y => Real.exp (c*f y)) x=Real.exp (c*varianceLogHeat c h f x) := by
  by_cases hc : c=0
  · subst c
    simp only [zero_mul,Real.exp_zero]
    unfold varianceHeat scaled
    simp
  · unfold varianceLogHeat
    rw [ite_eq_right hc]
    rw [mul_div_cancel₀ _ hc,Real.exp_log (varianceHeat_exp_pos hf c h x)]

lemma varianceTilted_lower_window {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : BoundedSmooth g) {c δ h r x M : ℝ}
    (hc : 0 ≤ c) (hf0 : ∀ y, 0 ≤ f y) (hg0 : ∀ y, 0 ≤ g y)
    (hδ : 0 < δ) (hδh : δ ≤ h) (hh1 : h ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : |x| ≤ 1) (hgwin : ∀ y, |y| ≤ r → 3/4 ≤ g y)
    (hden : varianceHeat h (fun y => Real.exp (c*f y)) x ≤ M) :
    ((3/2:ℝ)*(Real.sqrt (2*Real.pi))⁻¹*Real.exp (-2/δ)*r)/M ≤ varianceTilted c h f g x := by
  have hh0 := hδ.trans_le hδh
  have hM : 0 < M := (varianceHeat_exp_pos hf c h x).trans_le hden
  let k : ℝ := (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-2/δ)
  have hk : 0 ≤ k := by dsimp [k];positivity
  have hi := integrable_weighted_heatKernel hf hg c hh0 x
  have hnon (y : ℝ) : 0 ≤ heatKernel h (y-x)*(g y*Real.exp (c*f y)) :=
    mul_nonneg (heatKernel_pos hh0 _).le (mul_nonneg (hg0 y) (Real.exp_nonneg _))
  have hlower : (3/4:ℝ)*k*(2*r) ≤ ∫ y, heatKernel h (y-x)*(g y*Real.exp (c*f y)) := by
    have hm := setIntegral_mono_on (f := fun _ => (3/4:ℝ)*k)
      (s := Icc (-r) r) (integrableOn_const measure_Icc_lt_top.ne) hi.integrableOn measurableSet_Icc
      (fun y hy => by
        have hab : |y| ≤ r := abs_le.mpr hy
        have hw := heatKernel_uniform_lower hδ hδh hh1 hx (hab.trans hr1)
        have hg' := hgwin y hab
        have hex : 1 ≤ Real.exp (c*f y) := Real.one_le_exp_iff.mpr (mul_nonneg hc (hf0 y))
        have hge : (3/4:ℝ) ≤ g y*Real.exp (c*f y) := le_trans hg' (by nlinarith [hg0 y])
        change (3/4:ℝ)*k ≤ _
        rw [mul_comm (3/4:ℝ)]
        exact mul_le_mul hw hge (by norm_num) (heatKernel_pos hh0 _).le)
    have hs : ∫ _y in Icc (-r) r, (3/4:ℝ)*k = (3/4:ℝ)*k*(2*r) := by
      rw [setIntegral_const,Real.volume_real_Icc_of_le (neg_le_self hr0),smul_eq_mul]
      ring
    rw [hs] at hm
    exact hm.trans (setIntegral_le_integral hi (Eventually.of_forall hnon))
  have hgm := hg.smooth.continuous.measurable
  have hfm := hf.continuous.measurable
  unfold varianceTilted
  rw [varianceHeat_kernel (g := fun y => g y*Real.exp (c*f y)) (by fun_prop) hh0]
  have hn : 0 ≤ (3/4:ℝ)*k*(2*r) := by positivity
  have hd := div_le_div_of_nonneg_left hn (varianceHeat_exp_pos hf c h x) hden
  have hu := div_le_div_of_nonneg_right hlower (varianceHeat_exp_pos hf c h x).le
  have he : (3/2:ℝ)*(Real.sqrt (2*Real.pi))⁻¹*Real.exp (-2/δ)*r=(3/4:ℝ)*k*(2*r) := by dsimp [k];ring
  rw [he]
  exact hd.trans hu

end ZeroTemperatureSK.Heat

end
end

end OAI
