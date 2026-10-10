import OAI.Geometry.NodalSets.Charts.BallGeometry
import OAI.Geometry.NodalSets.Waves.RescaledGaussianField

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma rescaledGaussianField_sign (V : ι → Coord → ℂ) (S0 T0 S : Coord → ℝ)
    (N s sigma : ℝ) (x : Coord) (coeff : ι × Fin 2 → ℝ) (v : Coord)
    (hsigma : 0 < sigma) :
    (0 < rescaledGaussianField V S0 T0 S N s sigma x coeff v ↔
      0 < oscillatorySeed S0 T0 N (x+(N*s)⁻¹ • v)+
        gaussianWaveField V coeff (x+(N*s)⁻¹ • v)) ∧
    (rescaledGaussianField V S0 T0 S N s sigma x coeff v < 0 ↔
      oscillatorySeed S0 T0 N (x+(N*s)⁻¹ • v)+
        gaussianWaveField V coeff (x+(N*s)⁻¹ • v) < 0) := by
  have hden : 0 < sigma*Real.exp (fderiv ℝ S x v/s) := mul_pos hsigma (Real.exp_pos _)
  constructor
  · exact div_pos_iff_of_pos_right hden
  · change _ / _ < 0 ↔ _ < 0
    rw [div_lt_iff₀ hden,zero_mul]

lemma rescaled_sign_subballs_transfer (V : ι → Coord → ℂ) (S0 T0 S : Coord → ℝ)
    (N s sigma : ℝ) (x : Coord) (coeff : ι × Fin 2 → ℝ)
    (hscale : 0 < N*s) (hsigma : 0 < sigma) (tau r : ℝ) (j : Fin 4)
    (hpos : ∀ v : Coord, sourceEuclideanNorm v ≤ r →
      0 < rescaledGaussianField V S0 T0 S N s sigma x coeff v)
    (hneg : ∀ v : Coord, sourceEuclideanNorm (v-tau • Pi.single j 1) ≤ r →
      rescaledGaussianField V S0 T0 S N s sigma x coeff v < 0) :
    (∀ y : Coord, sourceEuclideanNorm (y-x) ≤ r/(N*s) →
      0 < oscillatorySeed S0 T0 N y+gaussianWaveField V coeff y) ∧
    (∀ y : Coord, sourceEuclideanNorm (y-(x+(N*s)⁻¹ • (tau • Pi.single j 1))) ≤ r/(N*s) →
      oscillatorySeed S0 T0 N y+gaussianWaveField V coeff y < 0) := by
  have he (y : Coord) : x+(N*s)⁻¹ • ((N*s) • (y-x)) = y := by
    rw [smul_smul,inv_mul_cancel₀ hscale.ne',one_smul,add_sub_cancel]
  constructor
  · intro y hy
    have hv : sourceEuclideanNorm ((N*s) • (y-x)) ≤ r := by
      rw [sourceEuclideanNorm_smul,abs_of_pos hscale]
      have hh := (le_div_iff₀ hscale).mp hy
      nlinarith
    have hh := (rescaledGaussianField_sign V S0 T0 S N s sigma x coeff _ hsigma).1.mp (hpos _ hv)
    simpa only [he] using hh
  · intro y hy
    have heq : (N*s) • (y-x)-tau • Pi.single j (1:ℝ) =
        (N*s) • (y-(x+(N*s)⁻¹ • (tau • Pi.single j 1))) := by
      have hid : (N*s)*((N*s)⁻¹*tau) = tau := by rw [← mul_assoc,mul_inv_cancel₀ hscale.ne',one_mul]
      simp only [smul_sub,smul_add,smul_smul,hid]
      abel
    have hv : sourceEuclideanNorm ((N*s) • (y-x)-tau • Pi.single j (1:ℝ)) ≤ r := by
      rw [heq,sourceEuclideanNorm_smul,abs_of_pos hscale]
      have hh := (le_div_iff₀ hscale).mp hy
      nlinarith
    have hh := (rescaledGaussianField_sign V S0 T0 S N s sigma x coeff _ hsigma).2.mp (hneg _ hv)
    simpa only [he] using hh

end
end Yau.Geometry

end OAI
