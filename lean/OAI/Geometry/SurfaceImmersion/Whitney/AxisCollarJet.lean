import OAI.Geometry.SurfaceImmersion.Whitney.ExactRegularCollar

namespace OAI

/-! The zero-parameter collar jet is the actual first derivative of the
outer map along the shared boundary. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma axis_collar_jet {f : Base → W} {V : ℝ × ℝ → W}
    (hf : ContDiff ℝ ∞ f)
    (hV0 : ∀ t, V (0,t) = axisTransverse f t) (t : ℝ) :
    homotopyCollarJet (axisValue f) V 0 t 0 0 = fderiv ℝ f (crosscapAxis t) := by
  calc
    _ = fderiv ℝ (transverseRuling f) (crosscapAxis t) := by
      ext v
      rw [transverseRuling_fderiv hf]
      simp [homotopyCollarJet, hV0, crosscapAxis_apply]
    _ = _ := transverseRuling_first_jet hf t

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
