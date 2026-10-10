import Mathlib
import OAI.Analysis.HardSphere.Geometry.KilledObservable

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
lemma killedTransition_continuous_ae (N : ℕ) (L : Length) (a t : ℝ)
    (g : C(Configuration N L,ℂ)) :
    killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g) =ᵐ[volume]
      killedAverage N L a t g := by
  have hgLp : MemLp (fun X ↦ g X) 2 (volume : Measure (Configuration N L)) :=
    MemLp.of_bound g.continuous.measurable.aestronglyMeasurable ‖g‖
      (Eventually.of_forall g.norm_coe_le_norm)
  have hge : ContinuousMap.toLp 2 volume ℂ g = hgLp.toLp g := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume g).trans hgLp.coeFn_toLp.symm
  rw [hge,killedTransition_bounded N L a t g.continuous.measurable
    hgLp (norm_nonneg g) g.norm_coe_le_norm]
  exact MemLp.coeFn_toLp _

end HardSphere

end

end OAI
