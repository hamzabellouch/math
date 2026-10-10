import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeatStrip
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierRemainder
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace OAI

/-! Each fixed Eisenstein row has an entire nonzero-mode sum. The
remaining continuation problem concerns the sum over the rows. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaNonzeroModes (c : Eisenstein) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' h : Eisenstein, if h=0 then 0 else
    cubicThetaRowFourierCoefficient c p.1 h*
      (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)

lemma cubicThetaNonzeroModes_differentiableOn_strip {c : Eisenstein} (hc : c≠0)
    {p : ℂ × ℝ} (hp : 0<p.2) (a b : ℝ) :
    DifferentiableOn ℂ (cubicThetaNonzeroModes c p) {s : ℂ | a<s.re ∧ s.re<b} := by
  let m (r : ℝ) (h : Eisenstein) := if h=0 then 0 else
    ∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat p.2 (r:ℂ) (cubicThetaRowHeatScale h) t‖
  let M : ℝ := Nat.card (Residues (3*c))
  have hm : Summable (fun h => M*(m a h+m b h)) :=
    ((cubicThetaNonzeroHeat_mass_summable hp (a:ℂ)).add
      (cubicThetaNonzeroHeat_mass_summable hp (b:ℂ))).mul_left M
  apply Complex.differentiableOn_tsum_of_summable_norm hm
  · intro h
    by_cases hh : h=0
    · simp only [hh,ite_true]
      exact differentiableOn_const _
    · simp only [ite_eq_right hh]
      exact ((cubicThetaNonzeroHeat_entire hp (cubicThetaRowHeatScale_pos hh)).const_mul
        (cubicThetaRowFourierCoefficient c p.1 h)).differentiableOn
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  · intro h s hs
    by_cases hh : h=0
    · simp [hh,m]
    · simp only [ite_eq_right hh,norm_mul,m]
      have hC : ‖cubicThetaRowFourierCoefficient c p.1 h‖≤M := by
        simpa only [cubicThetaRowFourierCoefficient,norm_mul,Circle.norm_coe,mul_one,M]
          using cubicThetaEisensteinGaussCoefficient_norm hc h
      exact mul_le_mul hC ((norm_integral_le_integral_norm _).trans
        (cubicThetaNonzeroHeat_mass_strip hp (cubicThetaRowHeatScale_pos hh) hs.1.le hs.2.le))
        (_root_.norm_nonneg _) (Nat.cast_nonneg _)

theorem cubicThetaNonzeroModes_entire {c : Eisenstein} (hc : c≠0)
    {p : ℂ × ℝ} (hp : 0<p.2) : Differentiable ℂ (cubicThetaNonzeroModes c p) := by
  intro s
  have hU : IsOpen {z : ℂ | s.re-1<z.re ∧ z.re<s.re+1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  exact (cubicThetaNonzeroModes_differentiableOn_strip hc hp (s.re-1) (s.re+1)).differentiableAt
    (hU.mem_nhds ⟨by linarith,by linarith⟩)

end CubicFirstMoment

end

end OAI
