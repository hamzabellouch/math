import Mathlib
import OAI.Probability.Perceptron.Pressure.EnrichedConcentration
import OAI.Probability.Perceptron.Pressure.EnrichedPatternMean
import OAI.Probability.Perceptron.Variational.MeasurableVariance

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def finitePatternRowsLaw (N M : ℕ) : Measure (Fin M → Fin N → ℝ) :=
  Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1

instance (N M : ℕ) : IsProbabilityMeasure (finitePatternRowsLaw N M) := by
  unfold finitePatternRowsLaw
  infer_instance

lemma enrichedExpectedLog_memLp (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    MemLp (enrichedExpectedLog n M k f p d u h z) 2 (finitePatternRowsLaw (n+1) M) := by
  obtain ⟨C,hC⟩ := enrichedExpectedLog_bounded n M k f p d u h z hz hz0 hz1
  exact MemLp.of_bound (enrichedExpectedLog_measurable n M k f p d u h z).aestronglyMeasurable
    C (ae_of_all _ hC)

lemma enrichedExpectedLog_variance (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    variance (enrichedExpectedLog n M k f p d u h z) (finitePatternRowsLaw (n+1) M) ≤
      (M:ℝ)*(2*‖f‖)^2 := by
  obtain ⟨C,hC⟩ := enrichedExpectedLog_bounded n M k f p d u h z hz hz0 hz1
  exact variance_pi_le_of_measurable_bounded_differences
    (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) M
    (enrichedExpectedLog_measurable n M k f p d u h z) hC
    (enrichedExpectedLog_update n M k f p d u h z hz hz0 hz1)

def enrichedFixedCountLog (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ)
    (a : (Fin M → Fin (n+1) → ℝ) ×
        (EnrichedMark (n+1) (n+1) p × DecoratedCascade (EnrichedMark (n+1) (n+1) p) k)) : ℝ :=
  enrichedCascadeLog n M k f a.1 p d u h a.2

lemma enrichedFixedCountLog_variance (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    let μ := (finitePatternRowsLaw (n+1) M).prod (enrichedDisorderLaw n k p z)
    MemLp (enrichedFixedCountLog n M k f p d u h) 2 μ ∧
      variance (enrichedFixedCountLog n M k f p d u h) μ ≤
        cascadeLogFluctuationConstant k z+(Real.pi^2/8)*
          ((enrichedFeatureBound (n+1) u:ℝ)*‖enrichedRootMap p d h‖)^2+(M:ℝ)*(2*‖f‖)^2 := by
  let μ := finitePatternRowsLaw (n+1) M
  let ν := enrichedDisorderLaw n k p z
  let F := enrichedFixedCountLog n M k f p d u h
  let G := enrichedExpectedLog n M k f p d u h z
  let K := cascadeLogFluctuationConstant k z+(Real.pi^2/8)*
    ((enrichedFeatureBound (n+1) u:ℝ)*‖enrichedRootMap p d h‖)^2
  have hG : MemLp G 2 μ := enrichedExpectedLog_memLp n M k f p d u h z hz hz0 hz1
  have hs (g : Fin M → Fin (n+1) → ℝ) :
      MemLp (fun a => F (g,a)) 2 ν ∧ variance (fun a => F (g,a)) ν ≤ K :=
    enrichedCascadeLog_fixed_patterns_variance n M k f g p d u h z hz hz0 hz1
  have hp : MemLp F 2 (μ.prod ν) := memLp_prod_of_conditional_square μ ν
    (enrichedCascadeLog_parameters_measurable n M k f p d u h z) hG K (fun g => (hs g).1)
    (fun g => by
      have hv := (hs g).2
      rw [variance_eq_integral (hs g).1.aestronglyMeasurable.aemeasurable] at hv
      exact hv)
  refine ⟨hp,?_⟩
  exact variance_prod_le_memLp μ ν hp (fun g => (hs g).1) hG (fun g => (hs g).2)
    (enrichedExpectedLog_variance n M k f p d u h z hz hz0 hz1)

end SphericalPerceptronFreeEnergy
end

end OAI
