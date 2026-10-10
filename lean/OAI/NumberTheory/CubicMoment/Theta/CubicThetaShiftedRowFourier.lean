import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedRowMellin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedHeatSummability
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowFourier

namespace OAI

/-! The actual inverted row Fourier expansion, with absolute integrated
summability proved before interchanging its heat integral and lattice sum. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaShiftedRowFourierCoefficient (b c : Eisenstein) (z : ℂ) (h : Eisenstein) : ℂ :=
  cubicThetaShiftedGaussCoefficient b c h*
    (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)

lemma cubicThetaShiftedWeightedHeat_summable {v : ℝ} (hv : 0<v) {s : ℂ}
    (hs : 1<s.re) {c : Eisenstein} (hc : primary c) (b : Eisenstein) (z : ℂ) :
    Summable (fun h : Eisenstein => ∫ t in Ioi (0:ℝ),
      ‖cubicThetaShiftedRowFourierCoefficient b c z h*
        cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t‖) := by
  have ht := (cubicThetaShiftedDualHeat_mass_summable hv hs).mul_left (Nat.card (Residues (3*c)):ℝ)
  apply ht.of_nonneg_of_le
  · intro h
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  · intro h
    simp_rw [cubicThetaShiftedRowFourierCoefficient,norm_mul,Circle.norm_coe,mul_one]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_right (cubicThetaShiftedGaussCoefficient_norm hc b h)
      (integral_nonneg (fun _ => _root_.norm_nonneg _))

lemma cubicThetaShiftedRowHeat_factor {t : ℝ} (ht : 0 < t) (v : ℝ) (s : ℂ) (h : Eisenstein) :
    (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
      ((Real.pi/t:ℝ)*(Real.exp
        (-4*Real.pi^2/t*Complex.normSq (cubicThetaShiftedRowFrequency h)):ℝ)) =
      (Real.pi:ℂ)*cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t := by
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
          (Real.exp (-4*Real.pi^2/t*Complex.normSq (cubicThetaShiftedRowFrequency h)):ℂ)) := by ring
    _ = _ := by
      rw [hp, ← Complex.ofReal_mul, ← Real.exp_add]
      unfold cubicThetaDualHeat cubicThetaShiftedRowHeatScale
      have he : -v^2*t + -4*Real.pi^2/t*Complex.normSq (cubicThetaShiftedRowFrequency h) =
          -v^2*t-(4*Real.pi^2*Complex.normSq (cubicThetaShiftedRowFrequency h))/t := by ring
      rw [he]
      ring

lemma cubicThetaShiftedRow_heat_poisson {c : Eisenstein} (hc : primary c)
    (b : Eisenstein) (z : ℂ) (v : ℝ) (s : ℂ) {t : ℝ} (ht : 0<t) :
    (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*cubicThetaShiftedCuspGaussianRow b c z t=
      (2*Real.pi/(81*Real.sqrt 3):ℂ)*∑' h : Eisenstein,
        cubicThetaShiftedRowFourierCoefficient b c z h*
          cubicThetaDualHeat v s (cubicThetaShiftedRowHeatScale h) t := by
  rw [cubicThetaShiftedCuspGaussianRow_poisson hc b z ht]
  simp only [←tsum_mul_left]
  apply tsum_congr
  intro h
  have he := cubicThetaShiftedRowHeat_factor ht v s h
  change (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
    ((2/(81*Real.sqrt 3):ℂ)*(cubicThetaShiftedGaussCoefficient b c h*
      (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)*
        ((Real.pi/t:ℝ)*(Real.exp
          (-4*Real.pi^2/t*Complex.normSq (cubicThetaShiftedRowFrequency h)):ℝ))))=_
  calc
    _ = (2/(81*Real.sqrt 3):ℂ)*cubicThetaShiftedRowFourierCoefficient b c z h*
        ((t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
          ((Real.pi/t:ℝ)*(Real.exp
            (-4*Real.pi^2/t*Complex.normSq (cubicThetaShiftedRowFrequency h)):ℝ))) := by
      unfold cubicThetaShiftedRowFourierCoefficient
      ring
    _ = _ := by rw [he]; ring

theorem cubicThetaShiftedRow_fourier (b : Eisenstein) {c : Eisenstein} (hc : primary c)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2<s.re) :
    Complex.Gamma s*cubicThetaShiftedRowSeries b c p s=
      ((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(81*Real.sqrt 3):ℂ)*
        ∑' h : Eisenstein, cubicThetaShiftedRowFourierCoefficient b c p.1 h*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  have hs1 : 1<s.re := by linarith
  have hFi (h : Eisenstein) : IntegrableOn (fun t =>
      cubicThetaShiftedRowFourierCoefficient b c p.1 h*
        cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t) (Ioi 0) := by
    apply (cubicThetaDualHeat_integrable hp hs1 _).const_mul
    by_cases hh : h=0
    · simp [hh]
    · exact (cubicThetaShiftedRowHeatScale_pos hh).le
  have hi := integral_tsum_of_summable_integral_norm hFi
    (cubicThetaShiftedWeightedHeat_summable hp hs1 hc b p.1)
  rw [cubicThetaShiftedRow_mellin b hc hp hs]
  calc
    _ = ((p.2/norm c:ℝ):ℂ)^s*((2*Real.pi/(81*Real.sqrt 3):ℂ)*
        ∫ t in Ioi (0:ℝ), ∑' h : Eisenstein,
          cubicThetaShiftedRowFourierCoefficient b c p.1 h*
            cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale h) t) := by
      congr 1
      rw [←integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => cubicThetaShiftedRow_heat_poisson hc b p.1 p.2 s ht)
    _ = _ := by
      rw [←hi]
      simp only [integral_const_mul,mul_assoc]

end CubicFirstMoment

end

end OAI
