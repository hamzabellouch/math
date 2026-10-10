import OAI.Analysis.LipschitzHilbert.Estimates.OperatorConjugation
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticePolarizationSpectrum

namespace OAI

/-! Addition and exact absorption of vertical multipliers on Schwartz
functions and their continuous L2 realizations. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem schwartzVerticalProjection_add_profile (p q : SchwartzMap ℝ ℂ) (w : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    schwartzVerticalProjection (p+q) w 0 f=
      schwartzVerticalProjection p w 0 f+schwartzVerticalProjection q w 0 f := by
  apply planar_schwartz_ext_fourier
  intro omega
  simp only [schwartzVerticalProjection_fourier,planarFourier_add,add_apply,add_mul]

theorem verticalL2Projection_add_profile (p q : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w) :
    verticalL2Projection (p+q) w=verticalL2Projection p w+verticalL2Projection q w := by
  have h := l2_maps_eq_onSchwartz ((verticalL2Projection (p+q) w).restrictScalars ℝ)
    ((verticalL2Projection p w+verticalL2Projection q w).restrictScalars ℝ) (fun f => by
      change verticalL2Projection (p+q) w (f.toLp 2 planeMeasure)=
        verticalL2Projection p w (f.toLp 2 planeMeasure)+verticalL2Projection q w (f.toLp 2 planeMeasure)
      rw [verticalL2Projection_onSchwartz _ _ hw,verticalL2Projection_onSchwartz _ _ hw,
        verticalL2Projection_onSchwartz _ _ hw,schwartzVerticalProjection_add_profile]
      exact map_add (SchwartzMap.toLpCLM ℂ ℂ 2 planeMeasure) _ _)
  apply ContinuousLinearMap.ext
  intro f
  exact congrArg (fun T : Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure => T f) h

theorem schwartzVerticalProjection_absorb (p q : SchwartzMap ℝ ℂ)
    (hpq : ∀ s, p s*q s=q s) (w : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    schwartzVerticalProjection p w 0 (schwartzVerticalProjection q w 0 f)=
      schwartzVerticalProjection q w 0 f := by
  apply planar_schwartz_ext_fourier
  intro omega
  simp only [schwartzVerticalProjection_fourier,←mul_assoc,hpq]

theorem verticalL2Projection_absorb (p q : SchwartzMap ℝ ℂ)
    (hpq : ∀ s, p s*q s=q s) (w : ℝ) (hw : 0<w) :
    (verticalL2Projection p w).comp (verticalL2Projection q w)=verticalL2Projection q w := by
  have h := l2_maps_eq_onSchwartz
    (((verticalL2Projection p w).comp (verticalL2Projection q w)).restrictScalars ℝ)
    ((verticalL2Projection q w).restrictScalars ℝ) (fun f => by
      change verticalL2Projection p w (verticalL2Projection q w (f.toLp 2 planeMeasure))=
        verticalL2Projection q w (f.toLp 2 planeMeasure)
      rw [verticalL2Projection_onSchwartz _ _ hw,verticalL2Projection_onSchwartz _ _ hw,
        schwartzVerticalProjection_absorb p q hpq])
  apply ContinuousLinearMap.ext
  intro f
  exact congrArg (fun T : Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure => T f) h

end LipschitzHilbert.PacketRepresentation

end

end OAI
