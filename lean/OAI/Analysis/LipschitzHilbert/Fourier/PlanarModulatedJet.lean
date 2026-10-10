import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketEnvelope

namespace OAI

/-! The three actual raw kernels for a general planar packet. The
covariant derivative differentiates its normalized vertical profile. -/

noncomputable section
namespace LipschitzHilbert

def planarProfileJet (f : SchwartzMap (ℝ × ℝ) ℂ) (ratio : ℝ)
    (i : Fin 3) : SchwartzMap (ℝ × ℝ) ℂ :=
  if i = 0 then f else if i = 1 then (ratio:ℂ) • planarVerticalDerivative f else
    (ratio:ℂ) • planarVerticalDerivative ((ratio:ℂ) • planarVerticalDerivative f)

def modulatedPlanarJet (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency scale y : ℝ) (hl : l ≠ 0) (i : Fin 3) : SchwartzMap ℝ ℂ :=
  modulatedPlanarSlice (planarProfileJet f (scale/W) i)
    a cy l W delta frequency y hl

theorem modulatedPlanarJet_covariant_zero (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency scale y : ℝ) (hl : l ≠ 0) (x : ℝ) :
    (scale:ℂ)*(deriv (fun t => modulatedPlanarJet f a cy l W delta frequency scale t hl 0 x) y -
      (frequency:ℂ)*Complex.I*modulatedPlanarJet f a cy l W delta frequency scale y hl 0 x) =
      modulatedPlanarJet f a cy l W delta frequency scale y hl 1 x := by
  simpa [modulatedPlanarJet,planarProfileJet] using
    modulatedPlanarSlice_covariant f a cy l W delta frequency scale y hl x

theorem modulatedPlanarJet_covariant_one (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency scale y : ℝ) (hl : l ≠ 0) (x : ℝ) :
    (scale:ℂ)*(deriv (fun t => modulatedPlanarJet f a cy l W delta frequency scale t hl 1 x) y -
      (frequency:ℂ)*Complex.I*modulatedPlanarJet f a cy l W delta frequency scale y hl 1 x) =
      modulatedPlanarJet f a cy l W delta frequency scale y hl 2 x := by
  simpa [modulatedPlanarJet,planarProfileJet] using
    modulatedPlanarSlice_covariant (((scale/W:ℝ):ℂ) • planarVerticalDerivative f)
      a cy l W delta frequency scale y hl x

theorem modulatedPlanarJet_continuous (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency scale : ℝ) (hl : l ≠ 0) (i : Fin 3) :
    Continuous (fun z : ℝ × ℝ => modulatedPlanarJet f a cy l W delta frequency scale z.1 hl i z.2) :=
  modulatedPlanarSlice_jointContinuous _ a cy l W delta frequency hl

theorem modulatedPlanarJet_differentiable (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency scale y : ℝ) (hl : l ≠ 0) (i : Fin 3) (x : ℝ) :
    DifferentiableAt ℝ (fun t => modulatedPlanarJet f a cy l W delta frequency scale t hl i x) y :=
  (modulatedPlanarSlice_vertical_hasDerivAt _ a cy l W delta frequency y hl x).differentiableAt

end LipschitzHilbert

end

end OAI
