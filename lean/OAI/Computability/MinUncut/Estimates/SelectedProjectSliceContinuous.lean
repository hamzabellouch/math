import Mathlib
import OAI.Computability.MinUncut.Estimates.FaceUpdateSelf
import OAI.Computability.MinUncut.Games.JointInner

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.RowNoise
open MeasureTheory GaussianHermite
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module BinaryFourier.F₂ W] [Fintype ι] [DecidableEq ι]
omit [AddCommGroup W] [Module BinaryFourier.F₂ W] in
lemma selectedProject_slice_continuous (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (B : R → W) (C : ι → ℝ) (x : ι) :
    Continuous (fun t => selectedProject J u B (Function.update C x t)) := by
  have hu : Continuous (fun t => Function.update C x t) := by
    apply continuous_pi
    intro y
    by_cases hy : y=x
    · subst y
      simp only [Function.update_self]
      exact continuous_id
    · simp only [Function.update_of_ne hy]
      exact continuous_const
  unfold selectedProject
  apply continuous_finsetSum
  intro j _
  simp only [maskHermite_eq]
  exact ((continuous_psi j.2).comp hu).mul_const _
end MinUncut.RowNoise

namespace MinUncut.Slice
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
lemma centeredClip_continuous (μ : Measure Ω) (A : ℝ) (f : Ω → ℝ) (hf : Continuous f) :
    Continuous (centeredClip μ A f) := by
  unfold centeredClip clip
  exact (continuous_const.max (hf.min continuous_const)).sub continuous_const
end MinUncut.Slice

end

end OAI
