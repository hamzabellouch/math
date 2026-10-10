import OAI.NumberTheory.Jacobsthal.Paths.TwoSidedThresholdArrival

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdOccurrence
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport FiniteHistoryOccurrence
open ArrivalKernelGeometry RegeneratingInverseBands CanonicalGapExposure
open TwoSidedThresholdArrival TwoSidedThresholdHazard TwoSidedThresholdKernel

noncomputable def thickOccurrence (v d e : ℝ) (N : ℕ) : Set (Hist CostState N) :=
  arrivalOccurrence (thickArrival v d e) N

theorem thickOccurrence_measurable (v d e : ℝ) (N : ℕ) : MeasurableSet (thickOccurrence v d e N) :=
  arrivalOccurrence_measurable (thickArrival_measurable v d e) N

theorem canonical_thick_occurrence_bound (v : ℝ) {d e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e)
    (s : State) (N : ℕ) :
    (finitePathMeasure s N).real (thickOccurrence v d e N) ≤
      thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*e) := by
  let E := thickArrival v d e
  have hE : MeasurableSet E := thickArrival_measurable v d e
  have hu := occurrence_le_integrated_hazards costKernel hE N (fun _ => (s,0))
  change (finitePathMeasure s N).real (thickOccurrence v d e N) ≤
    ∫ h,∑ j : Fin N,(costKernel (coordinate N h j.castSucc) E).toReal ∂finitePathMeasure s N at hu
  have hi : Integrable (fun h => ∑ j : Fin N,(costKernel (coordinate N h j.castSucc) E).toReal)
      (finitePathMeasure s N) := by
    apply integrable_finsetSum
    intro j _
    exact probability_integrable costKernel hE N (fun _ => (s,0)) j.castSucc
  have hb : ∀ᵐ h ∂finitePathMeasure s N,
      (∑ j : Fin N,(costKernel (coordinate N h j.castSucc) E).toReal) ≤
        thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*e) := by
    filter_upwards [canonical_total_thick_hazard v hd he s N] with h hh
    rw [Fin.sum_univ_castSucc] at hh
    have hn : 0 ≤ thickHazard (gapValue v (coordinate N h (Fin.last N))) d e (coordinate N h (Fin.last N)).1 := by
      rw [thickHazard_eq_actual]
      exact ENNReal.toReal_nonneg
    have hsum : (∑ j : Fin N,(costKernel (coordinate N h j.castSucc) E).toReal)=
        ∑ j : Fin N,thickHazard (gapValue v (coordinate N h j.castSucc)) d e (coordinate N h j.castSucc).1 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (thickHazard_eq_actual v d e _).symm
    rw [hsum]
    linarith
  have hh := integral_mono_ae hi (integrable_const (thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*e))) hb
  have hconst : (∫ _h : Hist CostState N,thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*e) ∂finitePathMeasure s N)=
      thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*e) := by simp
  rw [hconst] at hh
  exact hu.trans hh
end NumberTheoryLean.TwoSidedThresholdOccurrence

end

end Erdos970

end OAI
