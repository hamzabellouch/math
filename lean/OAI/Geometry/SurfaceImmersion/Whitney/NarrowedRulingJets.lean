import OAI.Geometry.SurfaceImmersion.Geometry.AxisFlatSecondJet
import OAI.Geometry.SurfaceImmersion.Geometry.TransverseSupport

namespace OAI

/-! The supported ruled correction retains the actual axis and all
 first and longitudinal second derivatives, for every cutoff width. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma narrowedRuling_axis (f : Base → ProjectionTarget 3) (η : ℝ → ℝ) (r t : ℝ) :
    narrowedRuling f η r (crosscapAxis t) = 0 := by
  simp [narrowedRuling,rulingRemainder_axis]

lemma narrowedRuling_first_jet {f : Base → ProjectionTarget 3} {η : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hη : ContDiff ℝ ∞ η) (r t : ℝ) :
    fderiv ℝ (narrowedRuling f η r) (crosscapAxis t) = 0 := by
  have hd := ((transverseCutoff_smooth r).differentiable (by simp) (crosscapAxis t)).hasFDerivAt.smul
    ((rulingRemainder_smooth hf hη).differentiable (by simp) (crosscapAxis t)).hasFDerivAt
  change HasFDerivAt (narrowedRuling f η r) _ (crosscapAxis t) at hd
  rw [hd.fderiv,rulingRemainder_first_jet hf hη,rulingRemainder_axis]
  simp

lemma narrowedRuling_retained_jets {f : Base → ProjectionTarget 3} {η : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hη : ContDiff ℝ ∞ η) (r t : ℝ) :
    (f+narrowedRuling f η r) (crosscapAxis t) = f (crosscapAxis t) ∧
    fderiv ℝ (f+narrowedRuling f η r) (crosscapAxis t) = fderiv ℝ f (crosscapAxis t) ∧
    axisDirectionJet (f+narrowedRuling f η r) (crosscapAxis t) = axisDirectionJet f (crosscapAxis t) := by
  exact ⟨by simp only [Pi.add_apply,narrowedRuling_axis,add_zero],
    axis_flat_add_first hf (narrowedRuling_smooth hf hη r) (narrowedRuling_first_jet hf hη r) t,
    axis_flat_add_direction hf (narrowedRuling_smooth hf hη r) (narrowedRuling_first_jet hf hη r) t⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
