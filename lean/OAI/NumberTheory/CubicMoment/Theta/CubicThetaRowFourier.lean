import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowMellin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaDualHeatSummability

namespace OAI

/-! The exact Fourier expansion of each nonzero Eisenstein row,
with the Fourier/Mellin interchange justified by an inverse-square majorant. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaRowFourierCoefficient (c : Eisenstein) (z : ℂ) (h : Eisenstein) : ℂ :=
  cubicThetaEisensteinGaussCoefficient c h*
    (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)

lemma cubicThetaRowHeat_factor {t : ℝ} (ht : 0 < t) (v : ℝ) (s : ℂ) (h : Eisenstein) :
    (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
      ((Real.pi/t:ℝ)*(Real.exp
        (-4*Real.pi^2/t*Complex.normSq (cubicThetaRowFrequency h)):ℝ)) =
      (Real.pi:ℂ)*cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t := by
  have hp : (t:ℂ)^(s-1)/(t:ℂ) = (t:ℂ)^(s-2) := by
    calc
      _ = (t:ℂ)^(s-1)/(t:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]
      _ = _ := by
        rw [← Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
        congr 1
        ring
  rw [Complex.ofReal_div]
  calc
    _ = (Real.pi:ℂ)*((t:ℂ)^(s-1)/(t:ℂ))*
        ((Real.exp (-v^2*t):ℂ)*
          (Real.exp (-4*Real.pi^2/t*Complex.normSq (cubicThetaRowFrequency h)):ℂ)) := by ring
    _ = _ := by
      rw [hp, ← Complex.ofReal_mul, ← Real.exp_add]
      unfold cubicThetaDualHeat cubicThetaRowHeatScale
      have he : -v^2*t + -4*Real.pi^2/t*Complex.normSq (cubicThetaRowFrequency h) =
          -v^2*t-(4*Real.pi^2*Complex.normSq (cubicThetaRowFrequency h))/t := by ring
      rw [he]
      ring

lemma cubicThetaEisensteinRow_heat_poisson {c : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (hc0 : c ≠ 0) (z : ℂ) (v : ℝ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*cubicThetaEisensteinGaussianRow c z t =
      (2*Real.pi/(9*Real.sqrt 3):ℂ)*∑' h : Eisenstein,
        cubicThetaRowFourierCoefficient c z h*cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t := by
  rw [cubicThetaEisensteinGaussianRow_poisson hc hc0 z ht]
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro h
  unfold cubicThetaRowFourierCoefficient
  have he := cubicThetaRowHeat_factor ht v s h
  change (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
    ((2/(9*Real.sqrt 3):ℂ)*(cubicThetaEisensteinGaussCoefficient c h*
      (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
        ((Real.pi/t:ℝ)*(Real.exp
          (-4*Real.pi^2/t*Complex.normSq (cubicThetaRowFrequency h)):ℝ)))) = _
  calc
    _ = (2/(9*Real.sqrt 3):ℂ)*cubicThetaRowFourierCoefficient c z h*
        ((t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
          ((Real.pi/t:ℝ)*(Real.exp
            (-4*Real.pi^2/t*Complex.normSq (cubicThetaRowFrequency h)):ℝ))) := by
      unfold cubicThetaRowFourierCoefficient
      ring
    _ = _ := by rw [he]; unfold cubicThetaRowFourierCoefficient; ring

theorem cubicThetaEisensteinRow_fourier {c : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (hc0 : c ≠ 0) {p : ℂ × ℝ} (hp : 0 < p.2) {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s*cubicThetaEisensteinRow c p s =
      ((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
        ∑' h : Eisenstein, cubicThetaRowFourierCoefficient c p.1 h*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  have hs1 : 1 < s.re := by linarith
  have hFi (h : Eisenstein) : IntegrableOn (fun t =>
      cubicThetaRowFourierCoefficient c p.1 h*
        cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) (Ioi 0) := by
    apply (cubicThetaDualHeat_integrable hp hs1 _).const_mul
    by_cases hh : h = 0
    · simp [hh]
    · exact (cubicThetaRowHeatScale_pos hh).le
  have hsum := cubicThetaWeightedDualHeat_mass_summable hp hs1 hc0 p.1
  have hi := integral_tsum_of_summable_integral_norm hFi hsum
  rw [cubicThetaEisensteinRow_mellin hc hc0 hp hs]
  calc
    _ = ((p.2/norm c:ℝ):ℂ)^s*((2*Real.pi/(9*Real.sqrt 3):ℂ)*
        ∫ t in Ioi (0:ℝ), ∑' h : Eisenstein, cubicThetaRowFourierCoefficient c p.1 h*
          cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
      congr 1
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => cubicThetaEisensteinRow_heat_poisson hc hc0 p.1 p.2 s ht)
    _ = _ := by
      rw [← hi]
      simp only [integral_const_mul, mul_assoc]

end CubicFirstMoment

end

end OAI
