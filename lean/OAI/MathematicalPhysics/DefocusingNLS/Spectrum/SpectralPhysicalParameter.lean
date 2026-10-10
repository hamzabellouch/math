import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralParameterShear
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalAnalytic

namespace OAI

/-! The logarithmic correction in differentiating the physical radial power
is exactly the normalized parameter shear. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

private theorem physicalJet_parameter (ν z : ℂ) (Y : ℂ → ℝ → ℂ × ℂ)
    (D : ℂ × ℂ) (r : ℝ)
    (hY : HasDerivAt (fun lam => Y lam (Real.log r)) D z) :
    HasDerivAt (fun lam => spectralPhysicalJet (ν - 2 * lam) (Y lam) r)
      (spectralPhysicalJet (ν - 2 * z)
        (fun t => (D.1 - 2 * (t : ℂ) * (Y z t).1,
          D.2 - 2 * (t : ℂ) * (Y z t).2 - 2 * (Y z t).1)) r) z := by
  have hp := (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt z hY
  have hq := (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt z hY
  have hν : HasDerivAt (fun lam : ℂ => ν - 2 * lam) (-2) z := by
    convert! (((hasDerivAt_id z).const_mul 2).const_sub ν) using 1
    simp only [mul_one]
  have hA := (hν.mul_const (Real.log r : ℂ)).cexp
  have hh := (hA.mul hp).prodMk
    ((hA.div_const (r : ℂ)).mul ((hν.mul hp).add hq))
  apply hh.congr_deriv
  apply Prod.ext
  all_goals
    dsimp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply]
    simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      spectralPhysicalJet, div_eq_mul_inv]
    ring

theorem spectralPhysicalPair_hasParameterDerivAt (νp νm z : ℂ)
    (Y : ℂ → ℝ → E₄) (D : ℝ → E₄) (r : ℝ)
    (hY : HasDerivAt (fun lam => Y lam (Real.log r)) (D (Real.log r)) z) :
    HasDerivAt (fun lam => spectralPhysicalPair (νp - 2 * lam) (νm - 2 * lam) (Y lam) r)
      (spectralPhysicalPair (νp - 2 * z) (νm - 2 * z)
        (fun t => circularParameterShear t (Y z t) (D t)) r) z := by
  have hp := (ContinuousLinearMap.fst ℂ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt z hY
  have hm := (ContinuousLinearMap.snd ℂ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt z hY
  have hdp := physicalJet_parameter νp z (fun lam t => (Y lam t).1)
    (D (Real.log r)).1 r hp
  have hdm := physicalJet_parameter νm z (fun lam t => (Y lam t).2)
    (D (Real.log r)).2 r hm
  apply (hdp.prodMk hdm).congr_deriv
  apply Prod.ext <;> apply Prod.ext
  all_goals
    simp only [spectralPhysicalPair, spectralPhysicalJet, circularParameterShear,
      Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      sub_zero]

end DefocusingNLS

end OAI
