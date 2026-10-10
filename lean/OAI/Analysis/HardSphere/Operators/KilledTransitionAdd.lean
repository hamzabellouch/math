import Mathlib
import OAI.Analysis.HardSphere.Conditioning.ReverseConfigurationPath
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
open Wiener
open scoped ComplexConjugate

theorem killedTransition_add (N : ℕ) (L : Length) (a s t : ℝ) (hs : 0<s) (ht : 0<t) :
    killedTransition N L a (s+t) = killedTransition N L a s ∘L killedTransition N L a t := by
  have hd := ContinuousMap.toLp_denseRange ℂ (volume : Measure (Configuration N L)) ℂ
    (show (2:ℝ≥0∞) ≠ ∞ by norm_num)
  apply ContinuousLinearMap.ext
  intro g
  change killedTransition N L a (s+t) g = killedTransition N L a s (killedTransition N L a t g)
  have hc : IsClosed {g : ScalarL2 N L | killedTransition N L a (s+t) g =
      killedTransition N L a s (killedTransition N L a t g)} :=
    isClosed_eq (ContinuousLinearMap.continuous _) ((ContinuousLinearMap.continuous _).comp
      (ContinuousLinearMap.continuous _))
  apply hc.closure_subset_iff.mpr ?_ (hd g)
  rintro _ ⟨g,rfl⟩
  change killedTransition N L a (s+t) (ContinuousMap.toLp 2 volume ℂ g) =
    killedTransition N L a s (killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g))
  have hgLp : MemLp (fun X ↦ g X) 2 (volume : Measure (Configuration N L)) :=
    MemLp.of_bound g.continuous.measurable.aestronglyMeasurable ‖g‖
      (Filter.Eventually.of_forall g.norm_coe_le_norm)
  have hge : ContinuousMap.toLp 2 volume ℂ g = hgLp.toLp g := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume g).trans hgLp.coeFn_toLp.symm
  rw [hge,killedTransition_bounded N L a (s+t) g.continuous.measurable hgLp (norm_nonneg _) g.norm_coe_le_norm,
    killedTransition_bounded N L a t g.continuous.measurable hgLp (norm_nonneg _) g.norm_coe_le_norm,
    killedTransition_bounded N L a s (killedAverage_measurable N L a t g.continuous.measurable)
      (killedAverage_memLp N L a t g.continuous.measurable (norm_nonneg _) g.norm_coe_le_norm)
      (norm_nonneg g) (killedAverage_bound N L a t (norm_nonneg _) g.norm_coe_le_norm)]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (killedAverage_add N L a s t hs ht g.continuous.measurable
    (norm_nonneg _) g.norm_coe_le_norm)

end HardSphere

namespace HardSphere
lemma killedTransition_nonneg (N : ℕ) (L : Length) (a t : ℝ) (ht : 0<t) :
    0 ≤ killedTransition N L a t := by
  have hh : 0<t/2 := by positivity
  rw [show t=t/2+t/2 by ring,killedTransition_add N L a (t/2) (t/2) hh hh]
  have ha := killedTransition_selfAdjoint N L a (t/2)
  have hp := ContinuousLinearMap.isPositive_adjoint_comp_self (killedTransition N L a (t/2))
  simpa only [show (killedTransition N L a (t/2)).adjoint=killedTransition N L a (t/2) from ha] using ContinuousLinearMap.nonneg_iff_isPositive.mpr hp

end HardSphere

end

end OAI
