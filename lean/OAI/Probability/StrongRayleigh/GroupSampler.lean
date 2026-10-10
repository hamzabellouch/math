import OAI.Probability.StrongRayleigh.GroupInnovationInverse
import OAI.Probability.StrongRayleigh.CanonicalInnovationSampler

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem336AdditiveD139.GroupSampler

universe u

abbrev Path := PathRealization.Path

local instance : MeasurableSpace Path := borel Path
local instance : BorelSpace Path := ⟨rfl⟩

variable {Γ : Type u} [Group Γ] [Countable Γ] [MeasurableSpace Γ] [DecidableEq Γ]

theorem factor_of_innovation_law
    (hresponse : ∀ (F : Type u) [Fintype F] [Nonempty F]
      (ν : ProbabilityMeasure (F → Bool)), StronglyRayleighFinite ν →
      ∀ (i : F) (h h' : F → ℝ) (D : ℝ), 0 ≤ D →
        (∀ j, |h j - h' j| ≤ D) → |tiltMean ν h i - tiltMean ν h' i| ≤ D / 2)
    (μ : ProbabilityMeasure (Γ → Bool))
    (hSR : StronglyRayleighCountable μ) (hInv : InvariantBinaryLaw μ)
    (ν : ProbabilityMeasure Path)
    (hν : IsPreBrownianReal (fun t (w : Path) => w t) (ν : Measure Path))
    (hlaw : (ReferenceObservation.law μ ν).map
      (fun ω => GroupInnovation.transform μ (PathRealization.referencePaths ω)) =
        Measure.infinitePi (fun _ : Γ => (ν : Measure Path))) :
    HasEquivariantIIDFactor μ := by
  apply PathRealization.factor_of_canonical_innovation_law μ ν hν
    (GroupInnovation.measurable_drift μ) 1 (GroupInnovation.abs_drift_le_one μ)
    (GroupInnovation.drift_mem_unitInterval μ) ((1 : ℝ) / 2) (by positivity)
  · intro t x y D hD hxy i
    simpa only [GroupInnovation.drift, div_eq_mul_inv, one_mul, mul_comm] using
      groupDrift_response_of_finite_response hresponse μ hSR t x y D hD hxy i
  · intro g t x i
    exact congrFun (groupDrift_leftTranslate μ hInv g t x) i
  · exact hlaw

end Problem336AdditiveD139.GroupSampler

end

end OAI
