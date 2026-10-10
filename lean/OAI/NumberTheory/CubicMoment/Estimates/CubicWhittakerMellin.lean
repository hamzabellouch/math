import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselMellin

namespace OAI

/-! The exact archimedean factor of the cubic theta Fourier expansion,
using the fixed Schläfli kernel and the normalization `4*pi*v`. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

/-- The heat-integral realization of `v*K_(1/3)(4*pi*v)`. -/
def cubicThetaWhittaker (v : ℝ) : ℂ :=
  (v:ℂ)/2*(cubicBesselKernel ((2*Real.pi*v)^2):ℂ)

lemma cubicThetaWhittaker_mellin {s : ℂ} (hs : 1/6 < s.re) :
    mellin cubicThetaWhittaker (2*s-1) =
      (1/4:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2*s)*
        Complex.Gamma (s+1/6)*Complex.Gamma (s-1/6) := by
  let f : ℝ → ℂ := fun x => (cubicBesselKernel x:ℂ)
  let c : ℝ := (2*Real.pi)^2
  have hc : 0 < c := by dsimp [c]; positivity
  have hform : cubicThetaWhittaker = fun v : ℝ =>
      (1/2:ℂ) • ((v:ℂ)^((1:ℝ):ℂ) • (fun x => f (c*x)) (v^(2:ℝ))) := by
    funext v
    simp only [cubicThetaWhittaker,Complex.ofReal_one,Complex.cpow_one,
      Real.rpow_two,f,c,smul_eq_mul]
    rw [show (2*Real.pi*v)^2 = (2*Real.pi)^2*v^2 by ring]
    ring
  rw [hform,mellin_const_smul,mellin_cpow_smul]
  simp only [smul_eq_mul]
  rw [show (2*s-1)+(1:ℝ)=2*s by push_cast; ring,
    mellin_comp_rpow (fun x => f (c*x)) (2*s) 2]
  norm_num only [Complex.ofReal_ofNat,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  simp only [Complex.real_smul]
  rw [show (2*s)/(2:ℂ)=s by ring,mellin_comp_mul_left f s hc,
    cubicBesselKernel_mellin hs]
  have hpow : (c:ℂ)^(-s) = ((2*Real.pi:ℝ):ℂ)^(-2*s) := by
    have he := Complex.cpow_mul_ofReal_nonneg
      (show (0:ℝ) ≤ 2*Real.pi by positivity) 2 (-s)
    simp only [Real.rpow_two,Complex.ofReal_ofNat] at he
    calc
      _ = ((2*Real.pi:ℝ):ℂ)^((2:ℂ)*(-s)) := he.symm
      _ = _ := by congr 1; ring
  rw [hpow]
  dsimp [f]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
