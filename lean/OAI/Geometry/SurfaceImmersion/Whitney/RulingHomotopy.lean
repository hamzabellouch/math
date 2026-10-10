import OAI.Geometry.SurfaceImmersion.Geometry.LinearMapHomotopy
import OAI.Geometry.SurfaceImmersion.Whitney.CompactCrosscapIsolation

namespace OAI

/-! The ruled deformation keeps the derivative-direction jets on the
entire axis and isolates each endpoint uniformly in its time parameter. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def rulingHomotopy (f : Base → ProjectionTarget 3) : ℝ → Base → ProjectionTarget 3 :=
  linearMapHomotopy f (transverseRuling f)

lemma rulingHomotopy_smooth {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (s : ℝ) : ContDiff ℝ ∞ (rulingHomotopy f s) :=
  linearMapHomotopy_smooth hf (transverseRuling_smooth hf) s

lemma rulingHomotopy_axis (f : Base → ProjectionTarget 3) (s t : ℝ) :
    rulingHomotopy f s (crosscapAxis t) = f (crosscapAxis t) :=
  linearMapHomotopy_fix (transverseRuling_axis f t) s

lemma rulingHomotopy_first_jet {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (s t : ℝ) :
    fderiv ℝ (rulingHomotopy f s) (crosscapAxis t) = fderiv ℝ f (crosscapAxis t) := by
  rw [rulingHomotopy,linearMapHomotopy_fderiv hf (transverseRuling_smooth hf),
    transverseRuling_first_jet hf,← add_smul]
  simp

lemma rulingHomotopy_direction_jet {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (s t : ℝ) :
    fderiv ℝ (surfaceDirection (rulingHomotopy f s) true) (crosscapAxis t,0) =
      fderiv ℝ (surfaceDirection f true) (crosscapAxis t,0) := by
  rw [rulingHomotopy,linearMapHomotopy_direction hf (transverseRuling_smooth hf),
    linearMapHomotopy_fderiv (surfaceDirection_smooth hf true)
      (surfaceDirection_smooth (transverseRuling_smooth hf) true),
    axisDirectionJet_surfaceDirection (transverseRuling_smooth hf),
    transverseRuling_direction_jet hf,← axisDirectionJet_surfaceDirection hf,← add_smul]
  simp

lemma rulingHomotopy_derivative_continuous {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) :
    Continuous (fun z : ℝ × Base => fderiv ℝ (rulingHomotopy f z.1) z.2) :=
  linearMapHomotopy_fderiv_continuous hf (transverseRuling_smooth hf)

lemma rulingHomotopy_direction_derivative_continuous {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) :
    Continuous (fun z : ℝ × (Base × ℝ) =>
      fderiv ℝ (surfaceDirection (rulingHomotopy f z.1) true) z.2) := by
  have he : (fun z : ℝ × (Base × ℝ) =>
      fderiv ℝ (surfaceDirection (rulingHomotopy f z.1) true) z.2) =
      (fun z => fderiv ℝ (linearMapHomotopy (surfaceDirection f true)
        (surfaceDirection (transverseRuling f) true) z.1) z.2) := by
    funext z
    rw [rulingHomotopy,linearMapHomotopy_direction hf (transverseRuling_smooth hf)]
  rw [he]
  exact linearMapHomotopy_fderiv_continuous (surfaceDirection_smooth hf true)
    (surfaceDirection_smooth (transverseRuling_smooth hf) true)

theorem rulingHomotopy_crosscap_isolation {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (t : ℝ)
    (hz : fderiv ℝ f (crosscapAxis t) (![0,1] : Base) = 0)
    (ht : fderiv ℝ f (crosscapAxis t) (![1,0] : Base) ≠ 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection f true) (crosscapAxis t,0))) :
    ∃ r : ℝ, 0 < r ∧ ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ ball (crosscapAxis t) r,
      (¬ Function.Injective (fderiv ℝ (rulingHomotopy f s) x) ↔ x = crosscapAxis t) :=
  compact_crosscap_isolation isCompact_Icc (rulingHomotopy f)
    (fun s _ => rulingHomotopy_smooth hf s) (rulingHomotopy_derivative_continuous hf)
    (rulingHomotopy_direction_derivative_continuous hf) (crosscapAxis t) _ _
    (fun s _ => rulingHomotopy_first_jet hf s t)
    (fun s _ => rulingHomotopy_direction_jet hf s t) hz ht hreg

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
