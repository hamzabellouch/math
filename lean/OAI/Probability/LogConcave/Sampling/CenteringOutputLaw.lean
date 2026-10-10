import Mathlib
import OAI.Probability.LogConcave.Dynamics.FlowRestrict

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

theorem centering_output_law {d : ℕ} {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    {K : Point d → Point d →L[ℝ] Point d} {M : Point d → Point d}
    (hM : Continuous M) (u : Point d) {s : ℝ} (hs : 0<s)
    {Ψ : (Point d × Point d) → ℝ → (Point d × Point d)}
    (hΨ : ∀p,Continuous (Ψ p) ∧ Ψ p 0=p ∧ ∀t∈Icc (0:ℝ) 1,
      HasDerivWithinAt (Ψ p) (skewCenteringField K (fun y => M y-u) s (Ψ p t)) (Icc (0:ℝ) 1) t)
    (hΨc : Continuous (fun p => Ψ p 1))
    (hΨlaw : (μ.prod (stdGaussian (Point d))).map (fun p => Ψ p 1)=μ.prod (stdGaussian (Point d))) :
    (μ.prod (stdGaussian (Point d))).map
      (fun p => s • p.2+∫t in (0:ℝ)..1,M (Ψ p t).1)=
      (stdGaussian (Point d)).map (fun g => u+s • g) := by
  have he : (fun p => s • p.2+∫t in (0:ℝ)..1,M (Ψ p t).1)=
      (fun p => u+s • (Ψ p 1).2) := by
    funext p
    simpa only [(hΨ p).2.1] using centering_momentum_identity hM u hs (hΨ p).1 (hΨ p).2.2
  rw [he]
  have hm : Measurable (fun p : Point d × Point d => u+s • p.2) := by fun_prop
  change (μ.prod (stdGaussian (Point d))).map
    ((fun p : Point d × Point d => u+s • p.2) ∘ (fun p => Ψ p 1)) = _
  rw [←Measure.map_map hm hΨc.measurable,hΨlaw]
  rw [show (fun p : Point d × Point d => u+s • p.2)=
    (fun g : Point d => u+s • g) ∘ Prod.snd from rfl,
    ←Measure.map_map (by fun_prop) measurable_snd,Measure.map_snd_prod,
    measure_univ,one_smul]
end LogConcaveSampling

end

end

end

end OAI
