import OAI.NumberTheory.CubicMoment.Estimates.UniformWeightMultiplier
import OAI.NumberTheory.CubicMoment.Estimates.LogDenominatorWeights

namespace OAI

/-! The literal reciprocal-log weight for an entire bounded smooth
family, with constants uniform over its members and norm scales. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

 def uniformLogDenominatorWeights {γ : Type*} {c : ℝ} (hc : 0 < c)
    {W : γ → ℝ → ℂ} (hW : UniformLogWeights W) :
    UniformLogWeights (fun z : γ × logWeightParameters c => logDenominatorWeight c (W z.1) z.2) := by
  let F : (ℝ × ℝ) → ℝ → ℂ :=
    fun p x => (smoothReciprocal c (p.1+p.2*smoothLog x):ℂ)
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
    have hD : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
        z.1.1+z.1.2*smoothLog z.2) := by
      have hL := smoothLog_smooth.comp
        (contDiff_snd : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => z.2))
      fun_prop
    exact Complex.ofRealCLM.contDiff.comp ((smoothReciprocal_smooth hc).comp hD)
  exact hW.compactMultiplier (logWeightParameters c) (logWeightParameters_compact c) F hF

 def uniformCoordinateLogDenominatorWeights {γ ι : Type*} [Fintype ι]
    {c : ℝ} (hc : 0 < c) {W : γ → ι → ℝ → ℂ}
    (hW : UniformLogWeights (fun z : γ × ι => W z.1 z.2)) :
    UniformLogWeights (fun z : (γ × (ι → logWeightParameters c)) × ι =>
      logDenominatorWeight c (W z.1.1 z.2) (z.1.2 z.2)) := by
  exact (uniformLogDenominatorWeights hc hW).reindex
    (fun z : (γ × (ι → logWeightParameters c)) × ι => ((z.1.1,z.2),z.1.2 z.2))

end CubicFirstMoment

end

end OAI
