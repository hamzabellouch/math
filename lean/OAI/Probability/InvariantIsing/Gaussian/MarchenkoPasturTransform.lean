import OAI.Probability.InvariantIsing.Gaussian.GaussianGramResolventEquation

namespace OAI

/-! The unique nonnegative solution of the real Marchenko--Pastur transform equation. -/
noncomputable section
namespace InvariantIsing

def marchenkoPasturTransform (t α : ℝ) : ℝ :=
  (-(t+α-1)+Real.sqrt ((t+α-1)^2+4*t))/(2*t)

def marchenkoPasturResidual (t α u : ℝ) : ℝ := 1-t*u-α*(u/(1+u))

lemma marchenkoPasturTransform_pos {t α : ℝ} (ht : 0 < t) : 0 < marchenkoPasturTransform t α := by
  have hs : (t+α-1)^2 < (t+α-1)^2+4*t := by linarith
  have ha := Real.lt_sqrt_of_sq_lt hs
  unfold marchenkoPasturTransform
  exact div_pos (by linarith) (by positivity)

lemma marchenkoPasturTransform_polynomial {t α : ℝ} (ht : 0 < t) :
    t*(marchenkoPasturTransform t α)^2+(t+α-1)*marchenkoPasturTransform t α-1 = 0 := by
  have hs := Real.sq_sqrt (show 0 ≤ (t+α-1)^2+4*t by positivity)
  rw [show 4*t=t*4 by ring] at hs
  unfold marchenkoPasturTransform
  field_simp [ht.ne']
  nlinarith

lemma marchenkoPasturTransform_equation {t α : ℝ} (ht : 0 < t) :
    marchenkoPasturResidual t α (marchenkoPasturTransform t α) = 0 := by
  have hp := marchenkoPasturTransform_polynomial (α := α) ht
  have hm := marchenkoPasturTransform_pos (α := α) ht
  unfold marchenkoPasturResidual
  apply (sub_eq_zero.mpr ?_)
  rw [← mul_div_assoc]
  apply (eq_div_iff (by linarith : 1+marchenkoPasturTransform t α ≠ 0)).mpr
  nlinarith

lemma nonnegative_fraction_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    u/(1+u) ≤ v/(1+v) := by
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

lemma nonnegative_fraction_lipschitz {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |u/(1+u)-v/(1+v)| ≤ |u-v| := by
  have hd : 0 < (1+u)*(1+v) := mul_pos (by linarith) (by linarith)
  have he : u/(1+u)-v/(1+v) = (u-v)/((1+u)*(1+v)) := by field_simp; ring
  rw [he,abs_div,abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have hd1 : 1 ≤ (1+u)*(1+v) := by nlinarith [mul_nonneg hu hv]
  nlinarith [abs_nonneg (u-v)]

lemma marchenkoPasturTransform_error {t α u : ℝ} (ht : 0 < t) (hα : 0 ≤ α) (hu : 0 ≤ u) :
    |u-marchenkoPasturTransform t α| ≤ |marchenkoPasturResidual t α u|/t := by
  let v := marchenkoPasturTransform t α
  have hv : 0 ≤ v := (marchenkoPasturTransform_pos ht).le
  have he : 1-t*v-α*(v/(1+v)) = 0 := marchenkoPasturTransform_equation ht
  apply (le_div_iff₀ ht).mpr
  rcases le_total u v with huv | hvu
  · rw [abs_of_nonpos (sub_nonpos.mpr huv)]
    have hf := mul_le_mul_of_nonneg_left (nonnegative_fraction_mono hu huv) hα
    have hr : 0 ≤ marchenkoPasturResidual t α u := by
      unfold marchenkoPasturResidual
      nlinarith
    rw [abs_of_nonneg hr]
    unfold marchenkoPasturResidual
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    have hf := mul_le_mul_of_nonneg_left (nonnegative_fraction_mono hv hvu) hα
    have hr : marchenkoPasturResidual t α u ≤ 0 := by
      unfold marchenkoPasturResidual
      nlinarith
    rw [abs_of_nonpos hr]
    unfold marchenkoPasturResidual
    nlinarith

lemma marchenkoPasturResidual_coefficient {t α β u : ℝ} (hu : 0 ≤ u) :
    |marchenkoPasturResidual t α u| ≤ |marchenkoPasturResidual t β u|+|α-β| := by
  have hf : |u/(1+u)| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hu (by linarith))]
    exact (div_le_one (by linarith)).mpr (by linarith)
  have he : marchenkoPasturResidual t α u =
      marchenkoPasturResidual t β u+(β-α)*(u/(1+u)) := by
    unfold marchenkoPasturResidual
    ring
  rw [he]
  calc
    _ ≤ |marchenkoPasturResidual t β u|+|(β-α)*(u/(1+u))| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul,abs_sub_comm β α]
      exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left hf (abs_nonneg (α-β))).trans_eq (mul_one _))

end InvariantIsing

end

end OAI
