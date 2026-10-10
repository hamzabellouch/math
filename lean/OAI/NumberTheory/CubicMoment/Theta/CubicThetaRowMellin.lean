import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowRadius
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowPoisson
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLaplaceSum

namespace OAI

/-! The Gaussian row identity integrated to the actual Eisenstein row
on its initial half-plane of absolute convergence. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaRowRadius_complex_power {c : Eisenstein} (hc : c ≠ 0)
    {p : ℂ × ℝ} (hp : 0 < p.2) (d : Eisenstein) (s : ℂ) :
    ((p.2/(Complex.normSq ((c:ℂ)*p.1+d)+norm c*p.2^2):ℝ):ℂ)^s =
      ((p.2/norm c:ℝ):ℂ)^s*(cubicThetaRowRadius c p d:ℂ)^(-s) := by
  have hN := norm_pos_of_ne_zero hc
  have hR := cubicThetaRowRadius_pos c d hp
  rw [← cubicThetaRowRadius_scale hc]
  rw [show p.2/(norm c*cubicThetaRowRadius c p d) =
    (p.2/norm c)/cubicThetaRowRadius c p d by ring]
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg (div_pos hp hN).le hR.le,
    div_eq_mul_inv, Complex.cpow_neg]

def cubicThetaEisensteinRow (c : Eisenstein) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' d : Eisenstein, cubicThetaEisensteinGridTerm (c,d) p s

theorem cubicThetaEisensteinRow_mellin {c : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (hc0 : c ≠ 0) {p : ℂ × ℝ} (hp : 0 < p.2) {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s*cubicThetaEisensteinRow c p s =
      ((p.2/norm c:ℝ):ℂ)^s*
        ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1)*(Real.exp (-p.2^2*t):ℂ)*
          cubicThetaEisensteinGaussianRow c p.1 t := by
  have hscale : cubicThetaEisensteinRow c p s =
      ((p.2/norm c:ℝ):ℂ)^s*∑' d : Eisenstein,
        cubicThetaEisensteinWeight c d*(cubicThetaRowRadius c p d:ℂ)^(-s) := by
    unfold cubicThetaEisensteinRow
    rw [← tsum_mul_left]
    apply tsum_congr
    intro d
    rw [cubicThetaEisensteinGridTerm_row hc, cubicThetaRowRadius_complex_power hc0 hp]
    ring
  have hM := cubicTheta_laplace_tsum (cubicThetaEisensteinWeight c)
    (cubicThetaRowRadius c p) (fun d => cubicThetaRowRadius_pos c d hp)
    (show 0 < s.re by linarith) (cubicThetaRowRadius_summable hc hc0 hp hs)
  rw [hscale, mul_left_comm, hM]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  unfold cubicThetaEisensteinGaussianRow
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro d
  have he : Real.exp (-cubicThetaRowRadius c p d*t) =
      Real.exp (-p.2^2*t)*Real.exp (-t*‖p.1+(d:ℂ)/(c:ℂ)‖^2) := by
    rw [← Real.exp_add]
    congr 1
    unfold cubicThetaRowRadius
    rw [Complex.normSq_eq_norm_sq]
    ring
  rw [he, Complex.ofReal_mul]
  ring

end CubicFirstMoment

end

end OAI
