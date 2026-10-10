import OAI.Probability.GaussianReplacement.Sampling

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
universe u
namespace CurrentProjection

namespace StreamKernel







def sharedSuccess {d M T : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (π : Measure Ξ) (K : Ξ → CompletedLearner d M T) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ, (K ξ).uniformSuccess ε ∂π



def StreamingMain (p₀ : ℝ≥0∞) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ)^2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1/10 →
    ∀ (Ξ : Type) [MeasurableSpace Ξ] [StandardBorelSpace Ξ]
      (π : Measure Ξ) [IsProbabilityMeasure π]
      (K : Ξ → CompletedLearner d (M d) T),
    AEMeasurable (fun ξ => (K ξ).uniformSuccess ε) π →
    p₀ ≤ sharedSuccess π K ε → c * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ)

end StreamKernel

def CriticalStreamingMain : Prop := StreamKernel.StreamingMain (3/5)
def LevelsStreamingMain : Prop := StreamKernel.StreamingMain (2/3)
def HybridStreamingMain : Prop := StreamKernel.StreamingMain (2/3)
def FiberStreamingMain : Prop := StreamKernel.StreamingMain (2/3)




end CurrentProjection

end

end OAI
