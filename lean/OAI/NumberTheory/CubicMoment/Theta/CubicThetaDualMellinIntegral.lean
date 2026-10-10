import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMellinPowers
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDirichletIntegral
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticKernelIntegrability

namespace OAI

/-! Convert the actual far-left dual Dirichlet integral into the literal
metaplectic transform, using absolute sum/integral interchange. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaDualMellinKernel (q : Eisenstein) (ℓ : ℤ) (W : ℝ→ℂ)
    (Z : ℝ) (s : ℂ) : ℂ :=
  cubicThetaDualPrefactor q*((cubicThetaDualScale q Z:ℂ)^s*
    metaplecticGammaQuotient ℓ s*mellin W s)

lemma cubicThetaDualMellinKernel_eq {q : Eisenstein} (hq : primary q)
    (ℓ : ℤ) (W : ℝ→ℂ) {Z : ℝ} (hZ : 0<Z) (s : ℂ) :
    cubicThetaDualMellinKernel q ℓ W Z s =
      mellin W s*(Z:ℂ)^s*(cubicThetaLevelScale q:ℂ)^(4*s-2)*
        ((2*Real.pi:ℝ):ℂ)^(4*s-2)*metaplecticGammaQuotient ℓ s := by
  calc
    _ = mellin W s*(cubicThetaDualPrefactor q*(cubicThetaDualScale q Z:ℂ)^s)*
        metaplecticGammaQuotient ℓ s := by unfold cubicThetaDualMellinKernel; ring
    _ = _ := by rw [←cubicTheta_archimedean_power hq hZ]; ring

lemma cubicThetaDualMellinKernel_integrable {q : Eisenstein} (hq : primary q)
    (ℓ : ℤ) (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {A Z : ℝ} (hA : 1/2<A) (hZ : 0<Z) :
    Integrable (fun t : ℝ => cubicThetaDualMellinKernel q ℓ W Z ((-A:ℂ)+(t:ℂ)*Complex.I)) := by
  have H := metaplecticKernel_integrable ℓ W hW hpos hsm (a := -A)
    (v := cubicThetaDualScale q Z) (by linarith) (cubicThetaDualScale_pos hq hZ)
  simpa only [cubicThetaDualMellinKernel,Complex.ofReal_neg] using
    H.const_mul (cubicThetaDualPrefactor q)

lemma cubicThetaDualMellinKernel_frequency {q : Eisenstein} (hq : primary q)
    (ℓ : ℤ) (W : ℝ→ℂ) {Z r : ℝ} (hZ : 0<Z) (hr : 0<r) (s : ℂ) :
    cubicThetaDualMellinKernel q ℓ W Z s*(r:ℂ)^(-(2*(1-s)-1)) =
      (cubicThetaDualPrefactor q*(r:ℂ)^(-1:ℂ))*
        (((cubicThetaDualScale q Z*r^2:ℝ):ℂ)^s*metaplecticGammaQuotient ℓ s*mellin W s) := by
  have hp := cubicTheta_dual_power hq hZ hr s
  rw [cubicTheta_archimedean_power hq hZ] at hp
  change cubicThetaDualPrefactor q*(cubicThetaDualScale q Z:ℂ)^s*
    (r:ℂ)^(-(2*(1-s)-1)) =
      cubicThetaDualPrefactor q*(r:ℂ)^(-1:ℂ)*
        ((cubicThetaDualScale q Z*r^2:ℝ):ℂ)^s at hp
  calc
    _ = (cubicThetaDualPrefactor q*(cubicThetaDualScale q Z:ℂ)^s*
        (r:ℂ)^(-(2*(1-s)-1)))*(metaplecticGammaQuotient ℓ s*mellin W s) := by
      unfold cubicThetaDualMellinKernel
      ring
    _ = _ := by rw [hp]; ring

lemma cubicThetaDualMellinKernel_frequency_integral {q : Eisenstein} (hq : primary q)
    (ℓ : ℤ) (W : ℝ→ℂ) {A Z r : ℝ} (hZ : 0<Z) (hr : 0<r) :
    (∫ t : ℝ, cubicThetaDualMellinKernel q ℓ W Z ((-A:ℂ)+(t:ℂ)*Complex.I)*
      (r:ℂ)^(-(2*(1-((-A:ℂ)+(t:ℂ)*Complex.I))-1))) =
      (cubicThetaDualPrefactor q*(r:ℂ)^(-1:ℂ))*
        ∫ t : ℝ, ((cubicThetaDualScale q Z*r^2:ℝ):ℂ)^((-A:ℂ)+(t:ℂ)*Complex.I)*
          metaplecticGammaQuotient ℓ ((-A:ℂ)+(t:ℂ)*Complex.I)*
            mellin W ((-A:ℂ)+(t:ℂ)*Complex.I) := by
  simp_rw [cubicThetaDualMellinKernel_frequency hq ℓ W hZ hr]
  rw [integral_const_mul]

theorem cubicTheta_dual_mellin_integral {q : Eisenstein} (hq : primary q)
    {a : Eisenstein→ℂ} {C : ℝ} (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C)
    (ℓ : ℤ) (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {A Z : ℝ} (hA : 1/2<A) (hZ : 0<Z) :
    ((1/(2*Real.pi):ℝ):ℂ)*(∫ t : ℝ,
      mellin W ((-A:ℂ)+(t:ℂ)*Complex.I)*(Z:ℂ)^((-A:ℂ)+(t:ℂ)*Complex.I)*
        (cubicThetaLevelScale q:ℂ)^(4*((-A:ℂ)+(t:ℂ)*Complex.I)-2)*
        ((2*Real.pi:ℝ):ℂ)^(4*((-A:ℂ)+(t:ℂ)*Complex.I)-2)*
        metaplecticGammaQuotient ℓ ((-A:ℂ)+(t:ℂ)*Complex.I)*
        cubicThetaDirichlet a (2*(1-((-A:ℂ)+(t:ℂ)*Complex.I))-1)) =
      cubicThetaDualPrefactor q*∑' n : MetaplecticDualArgument,
        a n.val/(‖cubicThetaFrequency n.val‖:ℂ)*
          metaplecticTransform ℓ W A
            (cubicThetaDualScale q Z*‖cubicThetaFrequency n.val‖^2) := by
  let H (t : ℝ) : ℂ := cubicThetaDualMellinKernel q ℓ W Z ((-A:ℂ)+(t:ℂ)*Complex.I)
  have hInt := cubicThetaDirichlet_integral hC ha (by linarith : 2<1+2*A)
    (fun t => 2*(1-((-A:ℂ)+(t:ℂ)*Complex.I))-1) (by fun_prop)
    (by intro t; simp; ring) H
    (cubicThetaDualMellinKernel_integrable hq ℓ W hW hpos hsm hA hZ)
  calc
    _ = ((1/(2*Real.pi):ℝ):ℂ)*(∫ t : ℝ,
        H t*cubicThetaDirichlet a (2*(1-((-A:ℂ)+(t:ℂ)*Complex.I))-1)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [H]
      rw [cubicThetaDualMellinKernel_eq hq ℓ W hZ]
    _ = ((1/(2*Real.pi):ℝ):ℂ)*∑' n : MetaplecticDualArgument,
        a n.val*∫ t : ℝ, H t*(‖cubicThetaFrequency n.val‖:ℂ)^
          (-(2*(1-((-A:ℂ)+(t:ℂ)*Complex.I))-1)) := by rw [hInt]
    _ = _ := by
      rw [←tsum_mul_left,←tsum_mul_left]
      apply tsum_congr
      intro n
      dsimp only [H]
      rw [cubicThetaDualMellinKernel_frequency_integral hq ℓ W hZ
        (cubicThetaFrequency_pos n.property),metaplecticTransform,Complex.cpow_neg_one]
      simp only [Complex.ofReal_neg]
      ring

theorem cubicTheta_dual_mellin_summable {q : Eisenstein} (hq : primary q)
    {a : Eisenstein→ℂ} {C : ℝ} (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C)
    (ℓ : ℤ) (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {A Z : ℝ} (hA : 1/2<A) (hZ : 0<Z) :
    Summable (fun n : MetaplecticDualArgument => a n.val/(‖cubicThetaFrequency n.val‖:ℂ)*
      metaplecticTransform ℓ W A (cubicThetaDualScale q Z*‖cubicThetaFrequency n.val‖^2)) := by
  have H := cubicThetaDirichlet_integral_summable hC ha (by linarith : 2<1+2*A)
    (fun t => 2*(1-((-A:ℂ)+(t:ℂ)*Complex.I))-1) (by intro t; simp; ring)
    (fun t => cubicThetaDualMellinKernel q ℓ W Z ((-A:ℂ)+(t:ℂ)*Complex.I))
    (cubicThetaDualMellinKernel_integrable hq ℓ W hW hpos hsm hA hZ)
  have H' : Summable (fun n : MetaplecticDualArgument => cubicThetaDualPrefactor q*
      (a n.val/(‖cubicThetaFrequency n.val‖:ℂ)*
        metaplecticTransform ℓ W A (cubicThetaDualScale q Z*‖cubicThetaFrequency n.val‖^2))) :=
    (H.mul_left ((1/(2*Real.pi):ℝ):ℂ)).congr (fun n => by
    rw [cubicThetaDualMellinKernel_frequency_integral hq ℓ W hZ
      (cubicThetaFrequency_pos n.property),Complex.cpow_neg_one]
    rw [metaplecticTransform]
    simp only [Complex.ofReal_neg]
    ring)
  exact (summable_mul_left_iff (cubicThetaDualPrefactor_ne_zero hq)).mp H'

end CubicFirstMoment

end

end OAI
