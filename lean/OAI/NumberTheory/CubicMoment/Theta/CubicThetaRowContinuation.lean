import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowEntire
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierCoefficients
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

namespace OAI

/-! Continuation of each individual Eisenstein row. Its nonzero modes
are entire; the constant mode can have a pole only at s=1. This does not
interchange continuation with the infinite sum over rows. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaNonzeroFourierRow_entire (c : Eisenstein)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    Differentiable ℂ (fun s => cubicThetaNonzeroFourierRow c p s) := by
  by_cases hc : (3:Eisenstein)∣c ∧ c≠0
  · have hbase : ((p.2/norm c:ℝ):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (div_pos hp (norm_pos_of_ne_zero hc.2)).ne'
    let _ : NeZero ((p.2/norm c:ℝ):ℂ) := ⟨hbase⟩
    change Differentiable ℂ (fun s => if (3:Eisenstein)∣c ∧ c≠0 then
      (((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
        cubicThetaNonzeroModes c p s)/Complex.Gamma s else 0)
    simp only [ite_eq_left hc]
    exact (((differentiable_const_cpow_of_neZero _).mul_const _).mul
      (cubicThetaNonzeroModes_entire hc.2 hp)).mul Complex.differentiable_one_div_Gamma
  · simp only [cubicThetaNonzeroFourierRow,ite_eq_right hc]
    exact differentiable_const 0

def cubicThetaRowContinuation (c : Eisenstein) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  (if c=0 then (p.2:ℂ)^s else 0)+
    (((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(p.2:ℂ)^(2-s))*
      cubicThetaFrequencyTerm s 0 c+cubicThetaNonzeroFourierRow c p s

theorem cubicThetaRowContinuation_right (c : Eisenstein) {p : ℂ × ℝ}
    (hp : 0<p.2) {s : ℂ} (hs : 2<s.re) :
    cubicThetaEisensteinRow c p s=cubicThetaRowContinuation c p s := by
  by_cases hc : c=0
  · subst c
    simp [cubicThetaRowContinuation,cubicThetaFrequencyTerm,
      cubicThetaNonzeroFourierRow,cubicThetaEisensteinRow_zero]
  · rw [cubicThetaEisensteinRow_split hc hp hs,
      cubicThetaConstantRow_eq hp (show 1<s.re by linarith)]
    simp only [cubicThetaRowContinuation,ite_eq_right hc,zero_add]
    rfl

lemma cubicThetaFrequencyTerm_entire (h c : Eisenstein) :
    Differentiable ℂ (fun s => cubicThetaFrequencyTerm s h c) := by
  by_cases hc : (3:Eisenstein)∣c ∧ c≠0
  · let _ : NeZero (norm c:ℂ) := ⟨Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hc.2).ne'⟩
    simp only [cubicThetaFrequencyTerm,ite_eq_left hc]
    exact ((differentiable_const_cpow_of_neZero _).comp differentiable_id.neg).const_mul _
  · simp only [cubicThetaFrequencyTerm,ite_eq_right hc]
    exact differentiable_const 0

theorem cubicThetaRowContinuation_differentiableAt (c : Eisenstein)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : s≠1) :
    DifferentiableAt ℂ (cubicThetaRowContinuation c p) s := by
  let _ : NeZero (p.2:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hp.ne'⟩
  have hpow := differentiable_const_cpow_of_neZero (p.2:ℂ)
  have hlead : DifferentiableAt ℂ (fun z : ℂ => if c=0 then (p.2:ℂ)^z else 0) s := by
    by_cases hc : c=0
    · simpa only [ite_eq_left hc] using hpow s
    · simp only [ite_eq_right hc]
      exact differentiableAt_const 0
  have hfactor : DifferentiableAt ℂ (fun z : ℂ =>
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(z-1))*(p.2:ℂ)^(2-z)) s :=
    ((differentiableAt_const _).div ((differentiable_id.sub_const (1:ℂ)) s)
      (sub_ne_zero.mpr hs)).mul
        ((hpow.comp ((differentiable_const 2).sub differentiable_id)) s)
  exact (hlead.add (hfactor.mul (cubicThetaFrequencyTerm_entire 0 c s))).add
    (cubicThetaNonzeroFourierRow_entire c hp s)

end CubicFirstMoment

end

end OAI
