import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarGaussian
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussianTail

namespace OAI

/-! A shift-independent error bound for scalar Poisson summation. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaTwistedGaussian_summable (χ : Eisenstein → ℂ)
    (hχ : ∀ a, ‖χ a‖≤1) {t : ℝ} (ht : 0<t) :
    Summable (fun a => χ a*(Real.exp (-t*norm a):ℂ)) := by
  have hA := residueHeckeScale_pos (q:=1) one_ne_zero
  have hs := principalLatticeTheta_summable (mul_pos ht hA)
  have hreal : Summable (fun a : Eisenstein => Real.exp (-t*norm a)) := by
    convert hs.norm using 1
    ext a
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    congr 1
    field_simp
  apply hreal.of_norm_bounded
  intro a
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (hχ a)

lemma cubicThetaTwistedGaussian_error (χ : Eisenstein → ℂ)
    (hχ : ∀ a, ‖χ a‖≤1) (h0 : χ 0=1) {t : ℝ} (ht : 0<t) :
    ‖(∑' a : Eisenstein,χ a*(Real.exp (-t*norm a):ℂ))-1‖ ≤
      cubicThetaLatticeGaussianTail t := by
  classical
  have hs := cubicThetaTwistedGaussian_summable χ hχ ht
  have he : (∑' a : Eisenstein,χ a*(Real.exp (-t*norm a):ℂ))-1=
      ∑' a : {a : Eisenstein // a≠0},χ a.val*(Real.exp (-t*norm a.val):ℂ) := by
    rw [hs.tsum_eq_add_tsum_ite 0]
    simp only [h0,show norm (0:Eisenstein)=0 by simp [norm],mul_zero,Real.exp_zero,Complex.ofReal_one,
      one_mul,add_sub_cancel_left]
    calc
      _ = ∑' a : Eisenstein,Set.indicator {a : Eisenstein | a≠0}
          (fun a => χ a*(Real.exp (-t*norm a):ℂ)) a := by
        apply tsum_congr
        intro a
        by_cases ha : a=0 <;> simp [ha,Set.indicator]
      _ = _ := (tsum_subtype {a : Eisenstein | a≠0}
        (fun a => χ a*(Real.exp (-t*norm a):ℂ))).symm
  rw [he]
  have hh := hs.subtype (fun a : Eisenstein => a≠0)
  calc
    _ ≤ ∑' a : {a : Eisenstein // a≠0},‖χ a.val*(Real.exp (-t*norm a.val):ℂ)‖ :=
      norm_tsum_le_tsum_norm hh.norm
    _ ≤ cubicThetaLatticeGaussianTail t := by
      apply hh.norm.tsum_le_tsum _ (cubicThetaLatticeGaussianTail_summable ht)
      intro a
      dsimp only [Function.comp_apply]
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (Real.exp_pos _).le (hχ a.val)

theorem cubicThetaScalarGaussian_error (z : ℂ) {t : ℝ} (ht : 0<t) :
    ‖cubicThetaScalarGaussian z t-(2*Real.pi/(9*Real.sqrt 3*t):ℝ)‖ ≤
      (2*Real.pi/(9*Real.sqrt 3*t))*
        cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*t)) := by
  let χ : Eisenstein → ℂ := fun h =>
    (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)
  have hχ (a : Eisenstein) : ‖χ a‖≤1 := by simp [χ]
  have h0 : χ 0=1 := by simp [χ,tracePair]
  have hk : 0≤2*Real.pi/(9*Real.sqrt 3*t) := by positivity
  have he := cubicThetaTwistedGaussian_error χ hχ h0 (t:=4*Real.pi^2/(27*t)) (by positivity)
  rw [cubicThetaScalarGaussian_poisson z ht,←mul_sub_one,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hk]
  exact mul_le_mul_of_nonneg_left he hk

end CubicFirstMoment

end

end OAI
