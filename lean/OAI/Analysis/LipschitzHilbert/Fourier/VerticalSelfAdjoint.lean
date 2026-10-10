import OAI.Analysis.LipschitzHilbert.Packets.VerticalFrameBound

namespace OAI

/-! Real vertical cutoffs are self-adjoint in complex L2. -/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem verticalProjection_inner_schwartz (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, conj (p s)=p s) (w : ℝ) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    inner ℂ ((schwartzVerticalProjection p w 0 f).toLp 2 planeMeasure) (g.toLp 2 planeMeasure)=
      inner ℂ (f.toLp 2 planeMeasure) ((schwartzVerticalProjection p w 0 g).toLp 2 planeMeasure) := by
  calc
    _ = ∫ z, inner ℂ (schwartzVerticalProjection p w 0 f z) (g z) ∂planeMeasure :=
      memLp_inner_integral planeMeasure _ _ ((schwartzVerticalProjection p w 0 f).memLp 2 planeMeasure) (g.memLp 2 planeMeasure)
    _ = ∫ z, inner ℂ (planarFourier (schwartzVerticalProjection p w 0 f) z) (planarFourier g z) ∂planeMeasure :=
      (planar_integral_inner_fourier _ _).symm
    _ = ∫ z, inner ℂ (planarFourier f z) (planarFourier (schwartzVerticalProjection p w 0 g) z) ∂planeMeasure := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [schwartzVerticalProjection_fourier,sub_zero,RCLike.inner_apply,map_mul,hp]
      ring
    _ = ∫ z, inner ℂ (f z) (schwartzVerticalProjection p w 0 g z) ∂planeMeasure :=
      planar_integral_inner_fourier _ _
    _ = _ := (memLp_inner_integral planeMeasure _ _ (f.memLp 2 planeMeasure)
      ((schwartzVerticalProjection p w 0 g).memLp 2 planeMeasure)).symm

theorem verticalL2Projection_inner (p : SchwartzMap ℝ ℂ) (hp : ∀ s, conj (p s)=p s)
    (w : ℝ) (hw : 0<w) (f g : Lp ℂ 2 planeMeasure) :
    inner ℂ (verticalL2Projection p w f) g=inner ℂ f (verticalL2Projection p w g) := by
  have hd : DenseRange (fun h : SchwartzMap (ℝ×ℝ) ℂ => h.toLp 2 planeMeasure) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  refine hd.induction_on₂ ?_ ?_ f g
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro F G
    rw [verticalL2Projection_onSchwartz _ _ hw,verticalL2Projection_onSchwartz _ _ hw]
    exact verticalProjection_inner_schwartz p hp w F G

end LipschitzHilbert.PacketRepresentation

end

end OAI
