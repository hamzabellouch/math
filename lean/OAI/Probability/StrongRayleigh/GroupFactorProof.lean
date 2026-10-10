import OAI.Probability.StrongRayleigh.GroupSampler
import OAI.Probability.StrongRayleigh.ReferenceInnovationLaw
import OAI.Probability.StrongRayleigh.ReferenceGroupPosterior
import OAI.Probability.StrongRayleigh.BrownianExistence

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Problem336AdditiveD139

universe u

local instance : MeasurableSpace PathRealization.Path := borel _
local instance : BorelSpace PathRealization.Path := ⟨rfl⟩

theorem group_innovation_map_eq
    {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]
    (μ : ProbabilityMeasure (Γ → Bool))
    (ν : ProbabilityMeasure PathRealization.Path)
    (hν : IsBrownianReal (fun t (w : PathRealization.Path) => w t)
      (ν : Measure PathRealization.Path)) :
    (ReferenceObservation.law μ ν).map
      (fun ω => GroupInnovation.transform μ (PathRealization.referencePaths ω)) =
        Measure.infinitePi (fun _ : Γ => (ν : Measure PathRealization.Path)) := by
  let B := fun (t : ℝ≥0) (w : PathRealization.Path) => w t
  have hBm : ∀ t, Measurable (B t) :=
    fun t => (continuous_eval_const t).measurable
  have hBj : Measurable (fun p : ℝ≥0 × PathRealization.Path => B p.1 p.2) :=
    (continuous_eval.comp (continuous_snd.prodMk continuous_fst)).measurable
  apply ReferenceInnovationLaw.map_field_innovation_eq μ ν B hν.toIsPreBrownianReal
    hBm hBj (fun w => w.continuous) (ν : Measure PathRealization.Path) hν
    (groupDrift μ) (measurable_groupDrift μ) (groupDrift_mem_Icc μ)
    (ReferenceObservation.groupDrift_condExp_history μ ν B hν.toIsPreBrownianReal hBm)
  intro ω i t
  rw [GroupInnovation.transform_apply_real_time]
  rfl

theorem group_factor_of_finite_response
    (hresponse : ∀ (F : Type u) [Fintype F] [Nonempty F]
      (ν : ProbabilityMeasure (F → Bool)), StronglyRayleighFinite ν →
      ∀ (i : F) (h h' : F → ℝ) (D : ℝ), 0 ≤ D →
        (∀ j, |h j - h' j| ≤ D) → |tiltMean ν h i - tiltMean ν h' i| ≤ D / 2)
    {Γ : Type u} [Group Γ] [Countable Γ] [MeasurableSpace Γ]
    (μ : ProbabilityMeasure (Γ → Bool))
    (hSR : StronglyRayleighCountable μ) (hInv : InvariantBinaryLaw μ) :
    HasEquivariantIIDFactor μ := by
  classical
  obtain ⟨ν, hν⟩ := BrownianConstruction.exists_brownianPathMeasure
  exact GroupSampler.factor_of_innovation_law hresponse μ hSR hInv ν
    hν.toIsPreBrownianReal (group_innovation_map_eq μ ν hν)

end Problem336AdditiveD139

end

end OAI
