import OAI.Analysis.LipschitzHilbert.Estimates.L2Conjugation
import OAI.Analysis.LipschitzHilbert.Fourier.ReflectedBandProjection
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalL2Projection
import OAI.Analysis.LipschitzHilbert.Estimates.L2Indicator

namespace OAI

/-! Conjugation identities extend from actual Schwartz integrals to
continuous L2 operators by density. -/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem verticalL2Projection_reflected (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w) :
    (verticalL2Projection (conjugateReflectedCutoff p) w).restrictScalars ℝ=
      (l2Conj planeMeasure).comp
        (((verticalL2Projection p w).restrictScalars ℝ).comp (l2Conj planeMeasure)) := by
  apply l2_maps_eq_onSchwartz
  intro f
  change verticalL2Projection (conjugateReflectedCutoff p) w (f.toLp 2 planeMeasure)=
    l2Conj planeMeasure (verticalL2Projection p w (l2Conj planeMeasure (f.toLp 2 planeMeasure)))
  rw [l2Conj_onSchwartz,verticalL2Projection_onSchwartz _ w hw,
    verticalL2Projection_onSchwartz _ w hw,l2Conj_onSchwartz,
    conjugateReflectedCutoff_projection]

theorem shortL2Operator_conjugate (K : ℝ → ℂ) (hKm : Measurable K) (hKi : Integrable K)
    (hK : ∀ t, conj (K t)=K t) (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) :
    ((shortL2Operator K hKm hKi u hu).restrictScalars ℝ).comp (l2Conj planeMeasure)=
      (l2Conj planeMeasure).comp ((shortL2Operator K hKm hKi u hu).restrictScalars ℝ) := by
  apply l2_maps_eq_onSchwartz
  intro f
  change shortL2Operator K hKm hKi u hu (l2Conj planeMeasure (f.toLp 2 planeMeasure))=
    l2Conj planeMeasure (shortL2Operator K hKm hKi u hu (f.toLp 2 planeMeasure))
  rw [l2Conj_onSchwartz,shortL2Operator_onSchwartz,shortL2Operator_onSchwartz]
  apply Lp.ext
  filter_upwards [(shortSchwartz_memLp K hKm hKi u hu (schwartzConj f)).coeFn_toLp,
    l2Conj_coe planeMeasure (shortSchwartzToL2 K hKm hKi u hu f),
    (shortSchwartz_memLp K hKm hKi u hu f).coeFn_toLp] with z hcf hc hf
  change (shortSchwartzToL2 K hKm hKi u hu (schwartzConj f)) z=_ at hcf
  change (shortSchwartzToL2 K hKm hKi u hu f) z=shortSlopeOperator K u f z at hf
  rw [hcf,hc,hf]
  exact shortSlopeOperator_conj K hK u f z

theorem l2Indicator_conjugate (S : Set (ℝ×ℝ)) (hS : MeasurableSet S) :
    ((l2Indicator planeMeasure S hS).restrictScalars ℝ).comp (l2Conj planeMeasure)=
      (l2Conj planeMeasure).comp ((l2Indicator planeMeasure S hS).restrictScalars ℝ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [l2Indicator_coe planeMeasure S hS (l2Conj planeMeasure f),
    l2Conj_coe planeMeasure f,l2Conj_coe planeMeasure (l2Indicator planeMeasure S hS f),
    l2Indicator_coe planeMeasure S hS f] with z hl hc hr hs
  change (l2Indicator planeMeasure S hS (l2Conj planeMeasure f)) z=
    (l2Conj planeMeasure (l2Indicator planeMeasure S hS f)) z
  rw [hl,hr,hs]
  by_cases hz : z∈S
  · simp only [Set.indicator_of_mem hz,hc]
  · simp only [Set.indicator_of_notMem hz,map_zero]

end LipschitzHilbert.PacketRepresentation

end

end OAI
