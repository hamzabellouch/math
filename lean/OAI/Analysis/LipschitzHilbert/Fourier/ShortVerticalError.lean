import OAI.Analysis.LipschitzHilbert.Fourier.ShortVerticalDifferenceL1
import OAI.Analysis.LipschitzHilbert.Estimates.ShortTimeAverageL1

namespace OAI

/-! The integrated very-short-time replacement error, with its exact
first-moment dependence. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def shortVerticalError (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) : ℂ :=
  ∫ t, if |t|≤1/4 then K t*shortVerticalDifference f u t z else 0

theorem shortVerticalDifference_joint_measurable (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (hu : Measurable u) :
    Measurable (fun p : ℝ×(ℝ×ℝ) => shortVerticalDifference f u p.1 p.2) := by
  unfold shortVerticalDifference
  exact (f.continuous.measurable.comp (by fun_prop)).sub
    (f.continuous.measurable.comp (by fun_prop))

theorem shortVerticalError_l1 (K : ℝ → ℂ) (hKm : Measurable K)
    (hK1 : Integrable (fun t => |t| *‖K t‖))
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Integrable (shortVerticalError K u f) planeMeasure ∧
      (∫ z, ‖shortVerticalError K u f z‖ ∂planeMeasure)≤
        4*(∫ t, |t| *‖K t‖)*(∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure) := by
  have h := shortTimeAverage_l1 K hKm hK1
    (fun p => shortVerticalDifference f u p.1 p.2)
    (shortVerticalDifference_joint_measurable f u hu.continuous.measurable)
    (4*∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure) (by positivity)
    (fun t ht => (shortVerticalDifference_l1 f u hu hub t ht).1)
    (fun t ht => (shortVerticalDifference_l1 f u hu hub t ht).2.trans_eq (by ring))
  exact ⟨h.1,h.2.trans_eq (by ring)⟩

theorem shortVerticalError_uniform (K : ℝ → ℂ)
    (hK1 : Integrable (fun t => |t| *‖K t‖))
    (u : (ℝ×ℝ) → ℝ) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (C : ℝ) (hC : 0≤C)
    (hDf : ∀ z, ‖verticalSchwartzDeriv f z‖≤C) (z : ℝ×ℝ) :
    ‖shortVerticalError K u f z‖≤(∫ t, |t| *‖K t‖)*C := by
  have h := norm_integral_le_of_norm_le (hK1.mul_const C)
    (Filter.Eventually.of_forall (fun t => show
      ‖if |t|≤1/4 then K t*shortVerticalDifference f u t z else 0‖≤(|t| *‖K t‖)*C from by
      by_cases ht : |t|≤1/4
      · rw [ite_eq_left ht,norm_mul]
        exact (mul_le_mul_of_nonneg_left (shortVerticalDifference_uniform f u hub t C hDf z)
          (norm_nonneg _)).trans_eq (by ring)
      · rw [ite_eq_right ht,norm_zero]
        positivity))
  simpa only [shortVerticalError,integral_mul_const] using h

theorem shortVerticalProjectionError_sizes (K : ℝ → ℂ) (hKm : Measurable K)
    (hK1 : Integrable (fun t => |t| *‖K t‖))
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (hub : ∀ z, |u z|≤1)
    (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1) :
    (∫ z, ‖shortVerticalError K u (schwartzVerticalProjection p w 0 f) z‖ ∂planeMeasure)≤
      (4*(∫ t, |t| *‖K t‖)*verticalProjectionCost (verticalDerivativeProfile p)/w)*
        (∫ z, ‖f z‖ ∂planeMeasure) ∧
    ∀ z, ‖shortVerticalError K u (schwartzVerticalProjection p w 0 f) z‖≤
      (∫ t, |t| *‖K t‖)*verticalProjectionCost (verticalDerivativeProfile p)/w := by
  have hD := verticalProjection_derivative_sizes p w hw f hf
  constructor
  · have h := (shortVerticalError_l1 K hKm hK1 u hu hub
      (schwartzVerticalProjection p w 0 f)).2
    exact h.trans ((mul_le_mul_of_nonneg_left hD.1 (by positivity)).trans_eq (by ring))
  · intro z
    have h := shortVerticalError_uniform K hK1 u hub (schwartzVerticalProjection p w 0 f)
      (verticalProjectionCost (verticalDerivativeProfile p)/w)
      (div_nonneg (verticalProjectionCost_pos _).le hw.le) hD.2 z
    exact h.trans_eq (by ring)

end LipschitzHilbert.PacketRepresentation

end

end OAI
