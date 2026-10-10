import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeatPowerSum
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFrequencyHolomorphic
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierNonzero

namespace OAI

/-! Quantitative cusp decay of the actual Eisenstein series after its
constant Fourier mode has been removed. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaFrequencyBound (s : ℂ) : ℝ :=
  9*(∑' c : Eisenstein, (norm c)^(-(s.re-1)))

lemma cubicThetaFrequencyBound_nonneg (s : ℂ) : 0 ≤ cubicThetaFrequencyBound s := by
  unfold cubicThetaFrequencyBound
  exact mul_nonneg (by norm_num) (tsum_nonneg (fun c => Real.rpow_nonneg (norm_nonneg c) _))

def cubicThetaNonzeroFrequencyTerm (p : ℂ × ℝ) (s : ℂ) (h : Eisenstein) : ℂ :=
  if h=0 then 0 else cubicThetaFrequencyDirichlet h s*
    (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
    (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)

lemma cubicThetaNonzeroFrequencyTerm_bound {p : ℂ × ℝ} {s : ℂ} (hs : 2<s.re)
    (h : Eisenstein) :
    ‖cubicThetaNonzeroFrequencyTerm p s h‖ ≤ cubicThetaFrequencyBound s*
      (if h=0 then 0 else ∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t‖) := by
  by_cases hh : h=0
  · simp [cubicThetaNonzeroFrequencyTerm,hh]
  · simp only [cubicThetaNonzeroFrequencyTerm,ite_eq_right hh,norm_mul,Circle.norm_coe,mul_one]
    exact mul_le_mul (cubicThetaFrequencyDirichlet_bound h hs)
      (norm_integral_le_integral_norm _) (_root_.norm_nonneg _) (cubicThetaFrequencyBound_nonneg s)

lemma cubicThetaNonzeroFrequencyTerm_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) : Summable (cubicThetaNonzeroFrequencyTerm p s) :=
  ((cubicThetaNonzeroHeat_mass_summable hp s).mul_left (cubicThetaFrequencyBound s)).of_norm_bounded
    (cubicThetaNonzeroFrequencyTerm_bound hs)

lemma cubicThetaNonzeroFrequencySum_bound {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) (k : ℕ) (hk : 1<(k:ℝ)) (hks : 0<s.re+(k:ℝ)-1) :
    ‖∑' h, cubicThetaNonzeroFrequencyTerm p s h‖ ≤
      (cubicThetaFrequencyBound s*cubicThetaHeatPowerConstant s k*
        (∑' h : Eisenstein, (norm h)^(-(k:ℝ))))*p.2^(-2*(s.re+(k:ℝ)-1)) := by
  calc
    _ ≤ ∑' h, ‖cubicThetaNonzeroFrequencyTerm p s h‖ :=
      norm_tsum_le_tsum_norm (cubicThetaNonzeroFrequencyTerm_summable hp hs).norm
    _ ≤ ∑' h : Eisenstein, cubicThetaFrequencyBound s*
        (if h=0 then 0 else ∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t‖) :=
      Summable.tsum_le_tsum (cubicThetaNonzeroFrequencyTerm_bound hs)
        (cubicThetaNonzeroFrequencyTerm_summable hp hs).norm
        ((cubicThetaNonzeroHeat_mass_summable hp s).mul_left _)
    _ ≤ _ := by
      rw [tsum_mul_left]
      have h := mul_le_mul_of_nonneg_left (cubicThetaNonzeroHeat_mass_height_bound hp s k hk hks)
        (cubicThetaFrequencyBound_nonneg s)
      convert h using 1
      ring

def cubicThetaCuspPowerConstant (s : ℂ) (k : ℕ) : ℝ :=
  ‖(2*Real.pi/(9*Real.sqrt 3):ℂ)/Complex.Gamma s‖*
    cubicThetaFrequencyBound s*cubicThetaHeatPowerConstant s k*
      (∑' h : Eisenstein, (norm h)^(-(k:ℝ)))

theorem cubicThetaEisenstein_cusp_power_bound {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) (k : ℕ) (hk : 1<(k:ℝ)) (hks : 0<s.re+(k:ℝ)-1) :
    ‖cubicThetaEisenstein p s-cubicThetaEisensteinConstantMode p.2 s‖ ≤
      cubicThetaCuspPowerConstant s k*p.2^(2-s.re-2*(k:ℝ)) := by
  have he := cubicThetaEisenstein_nonzero_coefficients hp hs
  change cubicThetaEisenstein p s=cubicThetaEisensteinConstantMode p.2 s+
    ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s/Complex.Gamma s)*
      (∑' h, cubicThetaNonzeroFrequencyTerm p s h) at he
  rw [he,add_sub_cancel_left,norm_mul]
  have hpre : ‖((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s/Complex.Gamma s)‖=
      ‖(2*Real.pi/(9*Real.sqrt 3):ℂ)/Complex.Gamma s‖*p.2^s.re := by
    rw [mul_div_right_comm,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp]
  rw [hpre]
  apply (mul_le_mul_of_nonneg_left (cubicThetaNonzeroFrequencySum_bound hp hs k hk hks)
    (mul_nonneg (_root_.norm_nonneg _) (Real.rpow_nonneg hp.le _))).trans_eq
  have hv : p.2^s.re*p.2^(-2*(s.re+(k:ℝ)-1))=p.2^(2-s.re-2*(k:ℝ)) := by
    rw [←Real.rpow_add hp]
    congr 1
    ring
  calc
    _ = cubicThetaCuspPowerConstant s k*(p.2^s.re*p.2^(-2*(s.re+(k:ℝ)-1))) := by
      unfold cubicThetaCuspPowerConstant
      ring
    _ = _ := by rw [hv]

end CubicFirstMoment

end

end OAI
