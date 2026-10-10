import OAI.Analysis.LipschitzHilbert.Fourier.VerticalL2Projection
import OAI.Analysis.LipschitzHilbert.Fourier.KernelPairing

namespace OAI

/-! Continuous L2 realization of the actual short-time band pairing. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def bandL2Operator (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (p : SchwartzMap ℝ ℂ) (w : ℝ) :
    Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  (shortL2Operator K hKm hK u hu).comp (verticalL2Projection p w)

def bandL2Pairing (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (p : SchwartzMap ℝ ℂ) (w : ℝ) :
    Lp ℂ 2 planeMeasure →L[ℝ] Lp ℂ 2 planeMeasure →L[ℝ] ℂ :=
  (isBoundedBilinearMap_inner (𝕜:=ℂ)).toContinuousLinearMap.flip.comp
    ((bandL2Operator K hKm hK u hu p w).restrictScalars ℝ)

theorem bandL2Operator_onSchwartz (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    bandL2Operator K hKm hK u hu p w (f.toLp 2 planeMeasure)=
      shortSchwartzToL2 K hKm hK u hu (schwartzVerticalProjection p w 0 f) := by
  change shortL2Operator K hKm hK u hu (verticalL2Projection p w (f.toLp 2 planeMeasure))=_
  rw [verticalL2Projection_onSchwartz p w hw,shortL2Operator_onSchwartz]

theorem bandL2Pairing_onSchwartz (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    bandL2Pairing K hKm hK u hu p w (f.toLp 2 planeMeasure) (g.toLp 2 planeMeasure)=
      ∫ z, shortSlopeOperator K u (schwartzVerticalProjection p w 0 f) z*star (g z) ∂planeMeasure := by
  change inner ℂ (g.toLp 2 planeMeasure) (bandL2Operator K hKm hK u hu p w (f.toLp 2 planeMeasure))=_
  rw [bandL2Operator_onSchwartz K hKm hK u hu p w hw]
  calc
    _ = ∫ z, inner ℂ (g z) (shortSlopeOperator K u (schwartzVerticalProjection p w 0 f) z) ∂planeMeasure :=
      memLp_inner_integral planeMeasure g (shortSlopeOperator K u (schwartzVerticalProjection p w 0 f))
        (g.memLp 2 planeMeasure) (shortSchwartz_memLp K hKm hK u hu _)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [RCLike.inner_apply, starRingEnd_apply, mul_comm]

theorem bandL2Pairing_kernel (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (hw : 0<w) (f g : SchwartzMap (ℝ×ℝ) ℂ) (l r : ℝ) (hwidth : r-l≤1/4)
    (hf : ∀ z, z.1∉Set.Icc l r → f z=0) (hg : ∀ z, z.1∉Set.Icc l r → g z=0) :
    bandL2Pairing K hKm hK u hu p w (f.toLp 2 planeMeasure) (g.toLp 2 planeMeasure)=
      kernelPairing K u (schwartzVerticalProjection p w 0 f) g := by
  rw [bandL2Pairing_onSchwartz K hKm hK u hu p w hw]
  have hp (z : ℝ×ℝ) (hz : z.1∉Set.Icc l r) : schwartzVerticalProjection p w 0 f z=0 := by
    rw [schwartzVerticalProjection_eq_convolution p w 0 hw]
    exact verticalConvolution_horizontal_support _ f _ hf z hz
  exact integral_congr_ae (Filter.Eventually.of_forall
    (shortSlopeOperator_pairing_eq K u _ g l r hwidth hp hg))

end LipschitzHilbert.PacketRepresentation

end

end OAI
