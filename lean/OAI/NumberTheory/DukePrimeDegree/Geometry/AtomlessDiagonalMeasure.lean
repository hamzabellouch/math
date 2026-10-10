import OAI.NumberTheory.DukePrimeDegree.Dynamics.SmallCentralizer
import OAI.NumberTheory.DukePrimeDegree.Entropy.CompactFutureLifts
import OAI.NumberTheory.DukePrimeDegree.Dynamics.DiagonalFlowMaximal
import Mathlib.Topology.Separation.Lemmas

namespace OAI

/-! # Diagonal-invariant probability measures have no point atoms -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma measure_singleton_eq_zero_of_continuous_orbit
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (x : Y) (f : ℝ → Y)
    (hf : Continuous f) (hf0 : f 0=x)
    (hmass : ∀ t, μ {f t}=μ {x}) (hne : ∃ t, f t ≠ x) : μ {x}=0 := by
  by_contra hx
  have hc : {y : Y | 0 < μ {y}}.Countable := by
    simpa only [id_eq,Set.ofPred_eq_eq_singleton] using
      (Measure.countable_meas_level_set_pos (μ := μ) (g := id) measurable_id)
  have hr : (range f).Countable := hc.mono (by
    rintro _ ⟨t,rfl⟩
    change 0 < μ {f t}
    rw [hmass]
    exact pos_iff_ne_zero.mpr hx)
  have hp : IsPreconnected (range f) := isPreconnected_range hf
  have hs : (range f).Subsingleton := hr.isTotallyDisconnected _ (subset_refl _) hp
  obtain ⟨t,ht⟩ := hne
  exact ht ((hs ⟨t,rfl⟩ ⟨0,rfl⟩).trans hf0)

/-- Only one nontrivial one-parameter diagonal flow is needed. -/
theorem nullSingletonClass_of_diagonal_invariant (d : ℕ)
    {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ) :
    NullSingletonClass μ := by
  let : MetricSpace (X (d+1)) := TopologicalSpace.metrizableSpaceMetric (X (d+1))
  let ell := rootContractionWeights i j
  let D := diagonalOneParameter ell (rootContractionWeights_sum i j)
  have hD : Continuous D := continuous_diagonalOneParameter ell _
  constructor
  intro x
  apply measure_singleton_eq_zero_of_continuous_orbit μ x (fun t => rightAction x (D t))
    ((continuous_rightAction_uncurry _).comp (continuous_const.prodMk hD))
    (by simp only [D,diagonalOneParameter_zero,rightAction_one])
  · intro t
    have hpres : MeasurePreserving (fun y => rightAction y (D t)) μ μ := by
      refine ⟨(continuous_rightAction _).measurable,?_⟩
      dsimp only [D]
      rw [diagonalOneParameter_eq_diagonalFlow]
      exact hA _
    have h := hpres.measure_preimage (measurableSet_singleton (rightAction x (D t))).nullMeasurableSet
    have he : (fun y => rightAction y (D t)) ⁻¹' {rightAction x (D t)}={x} := by
      ext y
      exact (rightActionHomeomorph (D t)).injective.eq_iff
    rw [he] at h
    exact h.symm
  · obtain ⟨r,hr,hinj⟩ := compact_uniform_chart_injective ({x} : Set (X (d+1))) isCompact_singleton
    have hnear : {t : ℝ | D t ∈ matrixBall (d+1) r} ∈ 𝓝 0 :=
      hD.continuousAt.preimage_mem_nhds
        ((matrixBall_isOpen _ _).mem_nhds (by simpa only [D,diagonalOneParameter_zero] using
          (one_mem_matrixBall (d+1) hr)))
    obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hnear
    have ht : 0 < δ/2 := by positivity
    have htm : D (δ/2) ∈ matrixBall (d+1) r := hsub (by
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht] using
        (show δ/2 < δ by linarith))
    refine ⟨δ/2,?_⟩
    intro heq
    have he : D (δ/2)=1 := hinj x (mem_singleton x) htm
      (one_mem_matrixBall (d+1) hr) (by simpa only [rightAction_one] using heq)
    have hei := congrArg (fun g : G (d+1) => g.val i i) he
    have hexp : Real.exp (δ/2)=1 := by
      simpa [D,ell,diagonalOneParameter,rootContractionWeights,hij] using hei
    have hz : δ/2=0 := Real.exp_injective (hexp.trans Real.exp_zero.symm)
    linarith

end DukePrimeDegree

end

end OAI
