import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularMode
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace OAI

/-! The radial Liouville transform used at unbounded spectral parameters. -/

open Set Filter Topology
namespace DefocusingNLS

noncomputable def homogeneousSpectralLocalizationFactor (h r : ℝ) : ℂ :=
  Complex.exp ((11 / 2 : ℂ) * (Real.log r : ℂ) + (h : ℂ) * Complex.I * (r : ℂ)^2 / 8)

noncomputable def homogeneousSpectralLocalizationSlope (h r : ℝ) : ℂ :=
  11 / (2 * (r : ℂ)) + (h : ℂ) * Complex.I * (r : ℂ) / 4

noncomputable def homogeneousSpectralLocalizationSlopeDeriv (h r : ℝ) : ℂ :=
  -11 / (2 * (r : ℂ)^2) + (h : ℂ) * Complex.I / 4

noncomputable def homogeneousSpectralLocalizationState (h : ℝ)
    (U : ℝ → ℂ × ℂ) (r : ℝ) : ℂ × ℂ :=
  (homogeneousSpectralLocalizationFactor h r * (U r).1,
    homogeneousSpectralLocalizationFactor h r *
      ((U r).2 + homogeneousSpectralLocalizationSlope h r * (U r).1))

theorem homogeneousSpectralLocalizationFactor_norm (h r : ℝ) (hr : 0 < r) :
    ‖homogeneousSpectralLocalizationFactor h r‖ = r ^ (11 / 2 : ℝ) := by
  rw [homogeneousSpectralLocalizationFactor, Complex.norm_exp, Real.rpow_def_of_pos hr]
  congr 1
  norm_num [Complex.add_re, Complex.mul_re, Complex.div_re, pow_two]
  ring

theorem homogeneousSpectralLocalizationFactor_hasDerivAt (h r : ℝ) (hr : 0 < r) :
    HasDerivAt (homogeneousSpectralLocalizationFactor h)
      (homogeneousSpectralLocalizationFactor h r * homogeneousSpectralLocalizationSlope h r) r := by
  have hlog := (Real.hasDerivAt_log hr.ne').ofReal_comp.const_mul (11 / 2 : ℂ)
  have hpoly := (((hasDerivAt_id r).ofReal_comp.pow 2).const_mul ((h : ℂ) * Complex.I)).div_const 8
  have hd := (hlog.add hpoly).cexp
  convert hd using 1
  · funext t
    rfl
  · dsimp only [homogeneousSpectralLocalizationFactor, homogeneousSpectralLocalizationSlope, id_eq,
      Pi.add_apply, Pi.pow_apply]
    push_cast
    field_simp [hr.ne']
    ring

theorem homogeneousSpectralLocalizationSlope_hasDerivAt (h r : ℝ) (hr : 0 < r) :
    HasDerivAt (homogeneousSpectralLocalizationSlope h)
      (homogeneousSpectralLocalizationSlopeDeriv h r) r := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hinv := ((hasDerivAt_id r).ofReal_comp.inv hrC).const_mul (11 / 2 : ℂ)
  have hlin := ((hasDerivAt_id r).ofReal_comp.const_mul ((h : ℂ) * Complex.I)).div_const 4
  convert hinv.add hlin using 1
  · funext t
    dsimp only [homogeneousSpectralLocalizationSlope, id_eq, Pi.add_apply, Pi.inv_apply]
    ring
  · dsimp only [homogeneousSpectralLocalizationSlopeDeriv, id_eq]
    push_cast
    field_simp [hrC]

theorem homogeneousSpectralLocalizationState_hasDerivAt
    (h r : ℝ) (hr : 0 < r) (U : ℝ → ℂ × ℂ) (K S : ℂ)
    (hU : HasDerivAt U ((U r).2,
      -2 * homogeneousSpectralLocalizationSlope h r * (U r).2 + K * (U r).1 + S) r) :
    HasDerivAt (homogeneousSpectralLocalizationState h U)
      ((homogeneousSpectralLocalizationState h U r).2,
        (K + homogeneousSpectralLocalizationSlopeDeriv h r +
          homogeneousSpectralLocalizationSlope h r ^ 2) *
            (homogeneousSpectralLocalizationState h U r).1 +
          homogeneousSpectralLocalizationFactor h r * S) r := by
  have hp := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hU
  have hm := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hU
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Function.comp_def] at hp hm
  have hA := homogeneousSpectralLocalizationFactor_hasDerivAt h r hr
  have hB := homogeneousSpectralLocalizationSlope_hasDerivAt h r hr
  convert (hA.mul hp).prodMk (hA.mul (hm.add (hB.mul hp))) using 1
  · rfl
  · apply Prod.ext <;> dsimp only [homogeneousSpectralLocalizationState,
      Function.comp_def, Pi.add_apply, Pi.mul_apply] <;> ring

theorem homogeneousSpectralLocalization_coefficient
    (h r a b eta : ℝ) (lam : ℂ) (hr : 0 < r) (hh : h^2 = 1) :
    (-(b : ℂ) - (h : ℂ) * Complex.I * ((a : ℂ) + lam) + (eta : ℂ) / (r : ℂ)^2) +
        homogeneousSpectralLocalizationSlopeDeriv h r + homogeneousSpectralLocalizationSlope h r ^ 2 =
      -(((r^2 / 16 + b - h * lam.im - (eta + 99 / 4) / r^2 : ℝ) : ℂ) +
        (h : ℂ) * Complex.I * ((a + lam.re - 3 : ℝ) : ℂ)) := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hhC : (h : ℂ)^2 = 1 := by exact_mod_cast hh
  have hlam : lam = (lam.re : ℂ) + Complex.I * (lam.im : ℂ) := by
    simpa only [mul_comm] using (Complex.re_add_im lam).symm
  conv_lhs => rw [hlam]
  dsimp only [homogeneousSpectralLocalizationSlope, homogeneousSpectralLocalizationSlopeDeriv]
  push_cast
  field_simp [hrC]
  ring_nf
  simp only [Complex.I_sq, hhC]
  ring

end DefocusingNLS

end OAI
