import Mathlib
import OAI.Probability.LogConcave.Analysis.InterpolationPotential

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal

lemma gaussian_marginal_lowerTail {d : ℕ} {P H : Point d → ℝ}
    (hP : Continuous P) (ht : HasGaussianLowerTail P) {a ρ : ℝ}
    (ha : 0<a) (hρ : ρ^2≤1)
    (hD : ∀y,(∫⁻z,ENNReal.ofReal (Real.exp (-P z-‖y-ρ • z‖^2/(2*a))))=
      ENNReal.ofReal (Real.exp (-H y))) : HasGaussianLowerTail H := by
  obtain ⟨m,hm,C,hC⟩ := ht
  let b := min m a⁻¹/4
  have hb : 0<b := div_pos (lt_min hm (inv_pos.mpr ha)) (by norm_num)
  have hb1 : 2*b≤ m/2 := by dsimp [b]; linarith [min_le_left m a⁻¹]
  have hb2 : 2*b≤1/(2*a) := by
    have he : a⁻¹/2=1/(2*a) := by field_simp
    rw [←he]
    dsimp [b]; linarith [min_le_right m a⁻¹]
  let J := ∫z : Point d,Real.exp (-(m/2)*‖z‖^2)
  have hJ : 0≤J := integral_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨b,hb,C+Real.log (J+1),fun y => ?_⟩
  have hpoint : ∀z : Point d,Real.exp (-P z-‖y-ρ • z‖^2/(2*a))≤
      Real.exp (C-b*‖y‖^2)*Real.exp (-(m/2)*‖z‖^2) := by
    intro z
    have hsum := norm_add_le (y-ρ • z) (ρ • z)
    rw [sub_add_cancel] at hsum
    have hy : ‖y‖^2≤2*‖y-ρ • z‖^2+2*‖z‖^2 := by
      have hs := pow_le_pow_left₀ (norm_nonneg y) hsum 2
      have hz : ‖ρ • z‖^2≤‖z‖^2 := by
        rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
        exact mul_le_of_le_one_left (sq_nonneg _) hρ
      nlinarith [sq_nonneg (‖y-ρ • z‖-‖ρ • z‖)]
    have hby := mul_le_mul_of_nonneg_left hy hb.le
    have h1 := mul_le_mul_of_nonneg_right hb1 (sq_nonneg ‖z‖)
    have h2 := mul_le_mul_of_nonneg_right hb2 (sq_nonneg ‖y-ρ • z‖)
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he : ‖y-ρ • z‖^2/(2*a)=(1/(2*a))*‖y-ρ • z‖^2 := by ring
    rw [he]
    nlinarith [hC z]
  have hbound : Integrable (fun z : Point d =>
      Real.exp (C-b*‖y‖^2)*Real.exp (-(m/2)*‖z‖^2)) :=
    (integrable_gaussian_envelope d (by positivity : 0 < m/2)).const_mul _
  have hk : Integrable (fun z : Point d => Real.exp (-P z-‖y-ρ • z‖^2/(2*a))) := by
    apply hbound.mono' (by fun_prop)
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hpoint z
  have he : (∫z,Real.exp (-P z-‖y-ρ • z‖^2/(2*a)))=Real.exp (-H y) := by
    have hh := hD y
    rw [←ofReal_integral_eq_lintegral_ofReal hk
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))] at hh
    have h := congrArg ENNReal.toReal hh
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun _ => (Real.exp_pos _).le)),
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  have hi := integral_mono hk hbound hpoint
  rw [he,integral_const_mul] at hi
  change Real.exp (-H y)≤Real.exp (C-b*‖y‖^2)*J at hi
  have hh : Real.exp (-H y)≤Real.exp (C-b*‖y‖^2+Real.log (J+1)) := by
    rw [Real.exp_add,Real.exp_log (by linarith : 0<J+1)]
    exact hi.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le)
  have := Real.exp_le_exp.mp hh
  linarith

lemma interpolationPotential_lowerTail {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2<1) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    HasGaussianLowerTail (interpolationPotential F x r ρ) := by
  have ha := (probability_time hρ0 hρ1).1
  apply gaussian_marginal_lowerTail (hF.continuous_potential x r)
    (hF.hasGaussianLowerTail x hr hl) ha (by linarith)
  intro y
  exact interpolation_density_integral hF x hr hl (by linarith) y

lemma interpolationPotential_smooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    ContDiff ℝ (⊤ : ℕ∞) (interpolationPotential F x r ρ) := by
  let g := fun y => y+(r*ρ) • conditionalFieldMean F x r ρ y
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    contDiff_id.add ((conditionalFieldMean_smooth hF x hr hl hρ0 hρ1).const_smul (r*ρ))
  have hd : ∀y,HasFDerivAt (interpolationPotential F x r ρ) ((innerSL ℝ) (g y)) y := by
    intro y
    exact (hasGradientAt_interpolationPotential hF x hr hl hρ0 hρ1 y).hasFDerivAt
  apply contDiff_infty_iff_fderiv.mpr
  refine ⟨fun y => (hd y).differentiableAt,?_⟩
  have he : fderiv ℝ (interpolationPotential F x r ρ)=fun y => (innerSL ℝ) (g y) :=
    funext (fun y => (hd y).fderiv)
  rw [he]
  exact (innerSL ℝ).contDiff.comp hg

lemma interpolationPotential_gradient_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    LipschitzWith (1+‖r*ρ‖₊*⟨(Real.pi^2/2)*ρ*((lam:ℝ)*r),by positivity⟩)
      (gradient (interpolationPotential F x r ρ)) := by
  have he := funext (interpolationPotential_gradient hF x hr hl hρ0 hρ1)
  rw [he]
  exact LipschitzWith.id.add ((lipschitzWith_smul (r*ρ)).comp (conditionalFieldMean_lipschitz hF x hr hl hρ0 hρ1))

end LogConcaveSampling

end

end

end

end OAI
