import OAI.Probability.PosteriorReplicas.Learners.JointKernelExperiment

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
universe u
namespace PosteriorRegression
namespace JointKernelExperiment
open Learner

local instance (d : ℕ) [NeZero d] : Nonempty (UnitSphere d) :=
  nonempty_of_isProbabilityMeasure (uniformSphere d)

def of_jointLaw {d M T : ℕ} [NeZero d] {Ω : Type u} [MeasurableSpace Ω]
    {ρ : Measure Ω} (rules : Ω → CompletedKernelLearner d M)
    (μ : Measure ((Ω × (UnitSphere d × Samples d T)) × UnitSphere d))
    [IsProbabilityMeasure μ]
    (hsem : ∀ᵐ ω ∂ρ, ∀ᵐ z ∂((uniformSphere d).prod (sampleLaw d T)),
      μ.condKernel (ω,z) = (rules ω).estimateLaw z.1 z.2) :
    JointKernelExperiment d M T Ω ρ where
  rules := rules
  outputKernel := μ.condKernel
  output_markov := inferInstance
  conditional_output := hsem

lemma of_jointLaw_law {d M T : ℕ} [NeZero d] {Ω : Type u} [MeasurableSpace Ω]
    {ρ : Measure Ω} (rules : Ω → CompletedKernelLearner d M)
    (μ : Measure ((Ω × (UnitSphere d × Samples d T)) × UnitSphere d))
    [IsProbabilityMeasure μ]
    (hsem : ∀ᵐ ω ∂ρ, ∀ᵐ z ∂((uniformSphere d).prod (sampleLaw d T)),
      μ.condKernel (ω,z) = (rules ω).estimateLaw z.1 z.2)
    (hmarg : μ.fst = ρ.prod ((uniformSphere d).prod (sampleLaw d T))) :
    (of_jointLaw rules μ hsem).law = μ := by
  change ρ.prod ((uniformSphere d).prod (sampleLaw d T)) ⊗ₘ μ.condKernel = μ
  rw [← hmarg, Measure.disintegrate μ μ.condKernel]

lemma of_jointLaw_success {d M T : ℕ} [NeZero d] {Ω : Type u} [MeasurableSpace Ω]
    {ρ : Measure Ω} (rules : Ω → CompletedKernelLearner d M)
    (μ : Measure ((Ω × (UnitSphere d × Samples d T)) × UnitSphere d))
    [IsProbabilityMeasure μ]
    (hsem : ∀ᵐ ω ∂ρ, ∀ᵐ z ∂((uniformSphere d).prod (sampleLaw d T)),
      μ.condKernel (ω,z) = (rules ω).estimateLaw z.1 z.2)
    (hmarg : μ.fst = ρ.prod ((uniformSphere d).prod (sampleLaw d T))) (ε : ℝ) :
    (of_jointLaw rules μ hsem).uniformSuccess ε =
      μ {z | angularError z.1.2.1 z.2 ≤ ε} := by
  rw [uniformSuccess, of_jointLaw_law rules μ hsem hmarg]

end JointKernelExperiment
end PosteriorRegression
end

end OAI
