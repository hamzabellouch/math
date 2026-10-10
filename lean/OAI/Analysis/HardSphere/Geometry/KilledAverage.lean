import Mathlib
import OAI.Analysis.HardSphere.Geometry.NormSqLpIntegral
import OAI.Analysis.HardSphere.Orbitals.StrongContractionLimitDense
import OAI.Analysis.HardSphere.Bridges.WienerStart

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

lemma killedAverage_zero (N : ℕ) (L : Length) (a : ℝ)
    (g : Configuration N L → ℂ) (X : Configuration N L) :
    killedAverage N L a 0 g X=(allowed N L a).indicator g X := by
  have h : ∀ w : CoordinatePaths N,
      killedObservable N L a g (freeTrajectory N L 0 w X)=(allowed N L a).indicator g X := by
    intro w
    rw [freeTrajectory_zero]
    by_cases hX : X∈allowed N L a
    · have ha : ContinuousMap.const Time X∈staysAllowed N L a := by
        rintro _ ⟨t,rfl⟩
        exact hX
      simp only [killedObservable,Set.indicator_of_mem ha,ContinuousMap.const_apply,
        Set.indicator_of_mem hX]
    · have ha : ContinuousMap.const Time X∉staysAllowed N L a :=
        fun h ↦ hX (h (Set.mem_range_self (0:Time)))
      simp only [killedObservable,Set.indicator_of_notMem ha,Set.indicator_of_notMem hX]
  simp only [killedAverage,h,integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]

lemma killedTransition_tendsto_zero_continuous (N : ℕ) (L : Length) (a : ℝ)
    (g : C(Configuration N L,ℂ)) :
    Tendsto (fun t : ℝ ↦ killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g))
      (𝓝 0) (𝓝 (killedTransition N L a 0 (ContinuousMap.toLp 2 volume ℂ g))) := by
  have hgLp : MemLp (fun X ↦ g X) 2 (volume : Measure (Configuration N L)) :=
    MemLp.of_bound g.continuous.measurable.aestronglyMeasurable ‖g‖
      (Eventually.of_forall g.norm_coe_le_norm)
  have hge : ContinuousMap.toLp 2 volume ℂ g = hgLp.toLp g := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume g).trans hgLp.coeFn_toLp.symm
  have hEq : ∀ t, killedTransition N L a t (ContinuousMap.toLp 2 volume ℂ g)=
      (killedAverage_memLp N L a t g.continuous.measurable (norm_nonneg g)
        g.norm_coe_le_norm).toLp (killedAverage N L a t g) := by
    intro t
    rw [hge]
    exact killedTransition_bounded N L a t g.continuous.measurable
      hgLp (norm_nonneg g) g.norm_coe_le_norm
  simp_rw [hEq]
  apply bounded_toLp_tendsto _ _ (norm_nonneg g)
    (fun t X ↦ killedAverage_bound N L a t (norm_nonneg g) g.norm_coe_le_norm X)
    (fun X ↦ killedAverage_bound N L a 0 (norm_nonneg g) g.norm_coe_le_norm X)
  apply Eventually.of_forall
  intro X
  rw [killedAverage_zero]
  exact killedAverage_tendsto_zero N L a g X

lemma killedTransition_tendsto_zero (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    Tendsto (fun t : ℝ ↦ killedTransition N L a t f) (𝓝 0)
      (𝓝 (killedTransition N L a 0 f)) := by
  exact strong_contraction_limit_of_dense (fun t ↦ killedTransition N L a t)
    (killedTransition N L a 0) (fun t ↦ killedTransition_apply_contraction N L a t)
    (killedTransition_apply_contraction N L a 0)
    (fun g : C(Configuration N L,ℂ) ↦ ContinuousMap.toLp 2 volume ℂ g)
    (ContinuousMap.toLp_denseRange ℂ volume ℂ (by norm_num : (2:ℝ≥0∞)≠∞))
    (killedTransition_tendsto_zero_continuous N L a) f

end HardSphere

end

end OAI
