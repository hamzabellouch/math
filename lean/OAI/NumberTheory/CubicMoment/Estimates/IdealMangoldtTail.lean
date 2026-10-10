import OAI.NumberTheory.CubicMoment.Estimates.IdealMangoldtContour
import OAI.NumberTheory.CubicMoment.Estimates.IdealLogDerivativeMajorant
import OAI.NumberTheory.CubicMoment.Estimates.MellinHeightTail
import OAI.NumberTheory.CubicMoment.Estimates.MellinWeightFamily

namespace OAI

/-! Quantitative tails of the actual prime Mellin integral. Constants are
uniform over a bounded real strip; the principal pole controls all twists. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def mellinScaledWeight (W : ℝ → ℂ) (X σ t : ℝ) : ℂ :=
  mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)*(X:ℂ)^((σ:ℂ)+(t:ℂ)*Complex.I)

lemma mellinScaledWeight_norm (W : ℝ → ℂ) {X : ℝ} (hX : 0 < X) (σ t : ℝ) :
    ‖mellinScaledWeight W X σ t‖=X^σ*‖mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)‖ := by
  simp only [mellinScaledWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,
    Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  ring

lemma mellinScaledWeight_integrable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) (σ : ℝ) : Integrable (mellinScaledWeight W X σ) := by
  let _ : NeZero (X:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hX.ne'⟩
  have hc : Continuous (mellinScaledWeight W X σ) := by
    unfold mellinScaledWeight
    exact ((smooth_mellin_entire W hW hpos hsm.continuous).continuous.comp
      (by fun_prop)).mul ((differentiable_const_cpow_of_neZero (X:ℂ)).continuous.comp
        (by fun_prop))
  exact (((smooth_mellin_vertical_integrable W hW hpos hsm σ).norm).const_mul (X^σ)).mono'
    hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun t => (mellinScaledWeight_norm W hX σ t).le))

lemma mellinScaledWeight_moment_integrable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) (σ : ℝ) (A : ℕ) :
    Integrable (fun t => |t|^A*‖mellinScaledWeight W X σ t‖) := by
  have hi := ((mellinVerticalSchwartz W hW hpos hsm σ).integrable_pow_mul volume A).const_mul (X^σ)
  convert hi using 1
  funext t
  rw [mellinScaledWeight_norm W hX,mellinVerticalSchwartz_apply,Real.norm_eq_abs]
  ring

theorem mellinScaledWeight_moment_bound (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ) (A : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ X σ : ℝ, 0 < X → |σ| ≤ M →
      (∫ t : ℝ, |t|^A*‖mellinScaledWeight W X σ t‖) ≤ K*X^σ := by
  obtain ⟨K,hK,hb⟩ := (uniformLogWeights_constant (ι := Unit) W hW hpos hsm).mellin_norm_moment M A
  refine ⟨K+1,by positivity,?_⟩
  intro X σ hX hσ
  have he : (∫ t : ℝ, |t|^A*‖mellinScaledWeight W X σ t‖)=
      X^σ*(∫ t : ℝ, |t|^A*‖mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)‖) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [mellinScaledWeight_norm W hX]
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (hb () σ hσ) (Real.rpow_nonneg hX.le σ)
  nlinarith [Real.rpow_pos_of_pos hX σ]

theorem idealMangoldt_right_tail
    (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃ C δ K : ℝ, 0 < C ∧ 0 < δ ∧ 0 < K ∧
      ∀ (χ : EisensteinIdealExponent → ℂ), (∀ ν, ‖χ ν‖ ≤ 1) →
      χ 0=1 → (∀ ν κ, χ (ν+κ)=χ ν*χ κ) →
      ∀ (L : ℂ → ℂ),
      (∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s) →
      ∀ X σ T : ℝ, 0 < X → 1 < σ → σ < 1+δ → σ ≤ 2 → 0 < T →
      ‖∫ t in (Icc (-T) T)ᶜ, idealMangoldtMellinIntegrand L W X (σ+(t:ℂ)*Complex.I)‖ ≤
        K*(1/(σ-1)+C)*X^σ/T^A := by
  obtain ⟨C,δ,hC,hδ,hline⟩ := idealLogDeriv_uniform_right_line
  obtain ⟨K,hK,hKbound⟩ := mellinScaledWeight_moment_bound W hW hpos hsm 2 A
  refine ⟨C,δ,K,hC,hδ,hK,?_⟩
  intro χ hχ hχ0 hχadd L hs X σ T hX hσ hσδ hσ2 hT
  have hB : 0 ≤ 1/(σ-1)+C := by positivity
  have hnorm : ∀ t : ℝ, ‖-logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤ 1/(σ-1)+C := by
    intro t
    rw [norm_neg]
    exact hline χ hχ hχ0 hχadd L hs σ t hσ hσδ
  have ht := bounded_product_height_tail (mellinScaledWeight W X σ)
    (fun t => -logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I))
    (mellinScaledWeight_integrable W hW hpos hsm hX σ) A
    (mellinScaledWeight_moment_integrable W hW hpos hsm hX σ A) hT hB hnorm
  change ‖∫ t in (Icc (-T) T)ᶜ,
      mellinScaledWeight W X σ t*(-logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I))‖ ≤ _
  calc
    _ ≤ ((1/(σ-1)+C)/T^A)*
        (∫ t : ℝ, |t|^A*‖mellinScaledWeight W X σ t‖) := ht
    _ ≤ ((1/(σ-1)+C)/T^A)*(K*X^σ) :=
      mul_le_mul_of_nonneg_left (hKbound X σ hX (by rw [abs_of_pos (by linarith)]; exact hσ2))
        (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
