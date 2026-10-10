import Mathlib
import OAI.Probability.SKSupport.Diffusion.FiniteTransition
import OAI.Probability.SKSupport.Density.DensityHeat
import OAI.Probability.SKSupport.Density.GaussianDecay

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma heatKernel_even (t x : ℝ) : heatKernel t (-x)=heatKernel t x := by
  simp only [heatKernel,gaussianPDFReal,sub_zero,neg_sq]

lemma heatKernel_measurable (t : ℝ) : Measurable (heatKernel t) := measurable_gaussianPDFReal 0 _

lemma integrable_gaussian_heat_product {f g : ℝ → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ExponentialBound f) (hg : ExponentialBound g) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-p.1^2/(2*a))*f p.1*heatKernel t (p.2-p.1)*g p.2)
      (volume.prod volume) := by
  obtain ⟨A,K,hA⟩ := hf
  obtain ⟨B,J,hB⟩ := hg
  let d := 1/(8*(a+t))
  have hd : 0 < d := by dsimp [d];positivity
  have hmajor := ((integrable_gaussian_linear hd K).mul_prod (integrable_gaussian_linear hd J)).const_mul
    ((A:ℝ)*(B:ℝ)*(Real.sqrt (2*Real.pi*t))⁻¹)
  apply hmajor.mono'
  · exact ((((measurable_id.fst.pow_const 2).neg.div_const (2*a)).exp.mul (hfm.comp measurable_fst)).mul
      ((heatKernel_measurable t).comp (measurable_snd.sub measurable_fst)) |>.mul (hgm.comp measurable_snd)).aestronglyMeasurable
  · filter_upwards [] with p
    simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (heatKernel_pos ht _)]
    have he := gaussian_convolution_quadratic ha ht p.1 p.2
    change d*(p.1^2+p.2^2) ≤ _ at he
    have hk := (heatKernel_pos ht (p.2-p.1)).le
    calc
      Real.exp (-p.1^2/(2*a))*|f p.1| * heatKernel t (p.2-p.1)*|g p.2| ≤
          Real.exp (-p.1^2/(2*a))*((A:ℝ)*Real.exp ((K:ℝ)*|p.1|))*heatKernel t (p.2-p.1)*
            ((B:ℝ)*Real.exp ((J:ℝ)*|p.2|)) := by
        apply mul_le_mul _ (hB p.2) (abs_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hA p.1) (Real.exp_nonneg _)) hk
      _ = ((A:ℝ)*(B:ℝ)*(Real.sqrt (2*Real.pi*t))⁻¹)*
          Real.exp (-p.1^2/(2*a)-(p.2-p.1)^2/(2*t)+(K:ℝ)*|p.1|+(J:ℝ)*|p.2|) := by
        rw [heatKernel_formula ht.le]
        simp only [sub_eq_add_neg,neg_div,Real.exp_add]
        ring
      _ ≤ ((A:ℝ)*(B:ℝ)*(Real.sqrt (2*Real.pi*t))⁻¹)*
          Real.exp ((-d*p.1^2+(K:ℝ)*|p.1|)+(-d*p.2^2+(J:ℝ)*|p.2|)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        simp only [neg_div]
        nlinarith only [he]
      _ = _ := by rw [Real.exp_add]

lemma gaussian_heat_pairing {f g : ℝ → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ExponentialBound f) (hg : ExponentialBound g) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (∫ x, (Real.exp (-x^2/(2*a))*f x)*varianceHeat t g x) =
      ∫ y, varianceHeat t (fun x => Real.exp (-x^2/(2*a))*f x) y*g y := by
  have hprod := integrable_gaussian_heat_product hfm hgm hf hg ha ht
  have hwm : Measurable (fun x : ℝ => Real.exp (-x^2/(2*a))*f x) := by fun_prop
  calc
    _ = ∫ x, ∫ y, Real.exp (-x^2/(2*a))*f x*heatKernel t (y-x)*g y := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [varianceHeat_kernel hgm ht,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = ∫ y, ∫ x, Real.exp (-x^2/(2*a))*f x*heatKernel t (y-x)*g y :=
      integral_integral_swap hprod
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [varianceHeat_kernel hwm ht,← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show y-x=-(x-y) by ring,heatKernel_even]
      ring

lemma gaussian_heat_forward_pairing {L g : ℝ → ℝ} {K : ℝ≥0} (hL : LipschitzWith K L)
    (hgm : Measurable g) (hg : ExponentialBound g) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    (∫ x, Real.exp (-x^2/(2*a)+L x)*varianceHeat t g x) =
      ∫ y, Real.exp (-y^2/(2*(a+t))+forwardCorrection a L t y)*g y := by
  have hf := exponentialBound_exp hL 1
  simp only [one_mul] at hf
  have hh := gaussian_heat_pairing hL.continuous.measurable.exp hgm hf hg ha ht
  have he : (fun x : ℝ => Real.exp (-x^2/(2*a))*Real.exp (L x))=
      fun x => Real.exp (-x^2/(2*a)+L x) := by funext x;rw [Real.exp_add]
  simp_rw [he,varianceHeat_gaussian_forwardCorrection hL ha ht] at hh
  simpa only [Real.exp_add] using hh

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma density_tilted_pairing {L f g : ℝ → ℝ} {K J : ℝ≥0}
    (hL : LipschitzWith K L) (hf : LipschitzWith J f) (hg : BoundedSmooth g)
    {a t c : ℝ} (ha : 0 < a) (ht : 0 < t) (hc : c ≠ 0) :
    (∫ x, Real.exp (c*varianceLogHeat c t f x-x^2/(2*a)+L x)*varianceTilted c t f g x)=
      ∫ y, Real.exp (c*f y-y^2/(2*(a+t))+forwardCorrection a L t y)*g y := by
  obtain ⟨G,hG⟩ := hg.bound
  have hwm : Measurable (fun y => g y*Real.exp (c*f y)) := by
    exact hg.smooth.continuous.measurable.mul ((measurable_const.mul hf.continuous.measurable).exp)
  have hw := (exponentialBound_exp hf c).bdd_mul hG
  calc
    _ = ∫ x, Real.exp (-x^2/(2*a)+L x)*varianceHeat t (fun y => g y*Real.exp (c*f y)) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show c*varianceLogHeat c t f x-x^2/(2*a)+L x=
        (-x^2/(2*a)+L x)+c*varianceLogHeat c t f x by ring]
      rw [Real.exp_add,exp_varianceLogHeat hf hc]
      unfold varianceTilted
      field_simp [ne_of_gt (varianceHeat_exp_pos hf c t x)]
    _ = ∫ y, Real.exp (-y^2/(2*(a+t))+forwardCorrection a L t y)*
        (g y*Real.exp (c*f y)) := gaussian_heat_forward_pairing hL hwm hw ha ht
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [sub_eq_add_neg,neg_div,Real.exp_add]
      ring

def finiteDensity (c : ℕ → ℝ≥0) (h : ℝ≥0) (f : ℝ → ℝ) (N i : ℕ) (x : ℝ) : ℝ :=
  Real.exp ((c i:ℝ)*backwardBoundary c h f N i x-x^2/(2*((i:ℝ)*h))+
    forwardBoundary c h f N i x)

lemma finiteDensity_step_pairing {f g : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (hg : BoundedSmooth g) (c : ℕ → ℝ≥0) (hc : ∀ i, 0 < (c i:ℝ))
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) {N i : ℕ} (hi : 0 < i) (hiN : i < N) :
    (∫ x, finiteDensity c h f N i x*varianceTilted (c i) h (backwardBoundary c h f N (i+1)) g x)=
      ∫ y, finiteDensity c h f N (i+1) y*g y := by
  obtain ⟨K,hK⟩ := (forwardBoundary_regular hf hLip c hh N i).exists_lipschitz
  have he := density_tilted_pairing hK (cascade_lipschitz hLip c h (N-(i+1)) (i+1)) hg
    (mul_pos (Nat.cast_pos.mpr hi) hh) hh (ne_of_gt (hc i))
  change (∫ x, Real.exp ((c i:ℝ)*varianceLogHeat (c i) h (backwardBoundary c h f N (i+1)) x-
    x^2/(2*((i:ℝ)*h))+forwardBoundary c h f N i x)*_) = _ at he
  rw [backwardBoundary_step hf hLip c h hiN] at he
  change (∫ x, finiteDensity c h f N i x*_) = _ at he
  refine he.trans ?_
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  unfold finiteDensity
  rw [forwardBoundary]
  dsimp only
  rw [ite_eq_right (Nat.ne_of_gt hi)]
  congr 1
  simp only [backwardBoundary,Nat.cast_add,Nat.cast_one]
  ring

end ZeroTemperatureSK.Heat

end
end

end OAI
