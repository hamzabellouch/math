import OAI.Geometry.SurfaceImmersion.Atlas.ParabolicPhaseChart
import OAI.Geometry.SurfaceImmersion.Atlas.CompactPhaseChart

namespace OAI

/-! One explicit nonlinear phase chart on a whole centered neighborhood. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def phaseCovectorSquare (ell : Base) : ℝ := ell.1^2+ell.2^2

lemma phaseCovectorSquare_pos {ell : Base} (hell : ell ≠ 0) : 0 < phaseCovectorSquare ell :=
  covector_length_sq_pos hell

def centeredPhaseCoordinates (ell : Base) (hell : ell ≠ 0) (c : Base) : Base ≃ₜ Base :=
  (Homeomorph.addRight (-c)).trans (phaseEquiv ell hell).toHomeomorph

lemma centeredPhaseCoordinates_apply (ell : Base) (hell : ell ≠ 0) (c x : Base) :
    centeredPhaseCoordinates ell hell c x = phaseEquiv ell hell (x-c) := by
  rfl

lemma centeredPhaseCoordinates_smooth (ell : Base) (hell : ell ≠ 0) (c : Base) :
    ContDiff ℝ ∞ (centeredPhaseCoordinates ell hell c) :=
  (phaseEquiv ell hell).contDiff.comp (contDiff_id.sub contDiff_const)

lemma centeredPhaseCoordinates_inverse_smooth (ell : Base) (hell : ell ≠ 0) (c : Base) :
    ContDiff ℝ ∞ (centeredPhaseCoordinates ell hell c).symm := by
  change ContDiff ℝ ∞ (fun x => (phaseEquiv ell hell).symm x - -c)
  exact (phaseEquiv ell hell).symm.contDiff.sub contDiff_const

def centeredParabolicChart (ell : Base) (hell : ell ≠ 0) (L : ℝ) (hL : L ≠ 0) (c : Base) :
    OpenPartialHomeomorph Base Base :=
  (centeredPhaseCoordinates ell hell c).transOpenPartialHomeomorph
    (parabolicPhaseChart (L/phaseCovectorSquare ell)
      (div_ne_zero hL (phaseCovectorSquare_pos hell).ne'))

lemma centeredParabolicChart_phase (ell : Base) (hell : ell ≠ 0) (L : ℝ) (hL : L ≠ 0)
    (c x : Base) :
    (centeredParabolicChart ell hell L hL c x).1 = centeredConvexPhase ell L c x := by
  change (parabolicPhaseMap (L/phaseCovectorSquare ell) (centeredPhaseCoordinates ell hell c x)).1 = _
  rw [centeredPhaseCoordinates_apply]
  simp only [parabolicPhaseMap,phaseEquiv_apply,Prod.fst_sub,Prod.snd_sub,
    centeredConvexPhase,convexQuadraticPhase,phaseLinear_apply,phaseCovectorSquare]
  have hA : ell.1^2+ell.2^2 ≠ 0 := (phaseCovectorSquare_pos hell).ne'
  field_simp [hA]
  ring

lemma centeredParabolicChart_smooth (ell : Base) (hell : ell ≠ 0) (L : ℝ) (hL : L ≠ 0)
    (c : Base) : ContDiff ℝ ∞ (centeredParabolicChart ell hell L hL c) :=
  (parabolicPhaseMap_smooth _).comp (centeredPhaseCoordinates_smooth ell hell c)

lemma centeredParabolicChart_inverse_smooth (ell : Base) (hell : ell ≠ 0)
    (L : ℝ) (hL : L ≠ 0) (c : Base) :
    ContDiffOn ℝ ∞ (centeredParabolicChart ell hell L hL c).symm
      (centeredParabolicChart ell hell L hL c).target := by
  exact (centeredPhaseCoordinates_inverse_smooth ell hell c).comp_contDiffOn
    (parabolicPhaseInverse_smooth _)

lemma centeredParabolicChart_source (ell : Base) (hell : ell ≠ 0) (L : ℝ) (hL : L ≠ 0)
    (c x : Base) :
    x ∈ (centeredParabolicChart ell hell L hL c).source ↔
      0 < phaseCovectorSquare ell+L*phaseLinear ell (x-c) := by
  change 0 < 1+(L/phaseCovectorSquare ell)*(phaseEquiv ell hell (x-c)).1 ↔ _
  rw [← mul_pos_iff_of_pos_left (phaseCovectorSquare_pos hell)]
  have hh : phaseCovectorSquare ell*(1+(L/phaseCovectorSquare ell)*(phaseEquiv ell hell (x-c)).1) =
      phaseCovectorSquare ell+L*phaseLinear ell (x-c) := by
    change phaseCovectorSquare ell*(1+(L/phaseCovectorSquare ell)*phaseLinear ell (x-c)) = _
    field_simp [(phaseCovectorSquare_pos hell).ne']
  rw [hh]

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
