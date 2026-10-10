import OAI.Geometry.SurfaceImmersion.Primitive.PhaseCrossingTransversality
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseOrdinaryCoordinates
import OAI.Geometry.SurfaceImmersion.Atlas.GenericAtlasPhases

namespace OAI

/-! The generic covectors selected in ordinary coordinates are the first
rows of the actual phase transitions. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates RealModes SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma phaseTransition_refl_first (q r : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (phi : M → ℝ) (hphi : ∀ p, (surfacePhaseChart r e p).1 = phi p) :
    Prod.fst ∘ surfacePhaseTransition q (OpenPartialHomeomorph.refl JetPolynomial.Base) r e =
      phi ∘ (coordinateChart q).symm := by
  funext x
  change (surfacePhaseChart r e
    ((surfacePhaseChart q (OpenPartialHomeomorph.refl JetPolynomial.Base)).symm x)).1 = _
  rw [surfacePhaseChart_refl_symm_apply,hphi]
  rfl

lemma phaseTransition_refl_covector (q r : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (phi : M → ℝ)
    (hphi : ∀ p, (surfacePhaseChart r e p).1 = phi p)
    {p : M} (hq : p ∈ (coordinateChart q).source)
    (hr : p ∈ (surfacePhaseChart r e).source) :
    firstCoordinateCovector
      (fderiv ℝ (surfacePhaseTransition q (OpenPartialHomeomorph.refl JetPolynomial.Base) r e)
        (coordinateChart q p)) =
      phaseDerivative (phi ∘ (coordinateChart q).symm) (coordinateChart q p) := by
  have hq' : p ∈ (surfacePhaseChart q (OpenPartialHomeomorph.refl JetPolynomial.Base)).source := by
    rwa [surfacePhaseChart_refl_source]
  have hs := surfacePhaseTransition_source q r (OpenPartialHomeomorph.refl JetPolynomial.Base) e hq' hr
  have ht := ((surfacePhaseTransition_smooth q (OpenPartialHomeomorph.refl JetPolynomial.Base)
    contDiff_id r e he) _ hs).contDiffAt
      ((surfacePhaseTransition q (OpenPartialHomeomorph.refl JetPolynomial.Base) r e).open_source.mem_nhds hs)
  have hh := phaseDerivative_fst (ht.differentiableAt (by simp))
  rw [phaseTransition_refl_first q r e phi hphi] at hh
  exact hh.symm

omit [IsManifold planeModel ∞ M] in
lemma centeredPhase_first (q : M) (ell : Base) (L : ℝ)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ∀ x, (baseEquiv (e x)).1 =
      centeredConvexPhase ell L (coordinateChart q q) (baseEquiv x)) (p : M) :
    (surfacePhaseChart q e p).1 = centeredAtlasPhase q ell L p := by
  rw [surfacePhaseChart_apply,he]
  rfl

 theorem generic_phase_crossing_first_nonzero (q q₁ q₂ : M)
    (e₁ e₂ : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he₁ : ContDiff ℝ ∞ e₁) (hi₁ : ContDiff ℝ ∞ e₁.symm)
    (he₂ : ContDiff ℝ ∞ e₂)
    (phi₁ phi₂ : M → ℝ)
    (hphi₁ : ∀ p, (surfacePhaseChart q₁ e₁ p).1 = phi₁ p)
    (hphi₂ : ∀ p, (surfacePhaseChart q₂ e₂ p).1 = phi₂ p)
    {p : M} (hq : p ∈ (coordinateChart q).source)
    (h₁ : p ∈ (surfacePhaseChart q₁ e₁).source)
    (h₂ : p ∈ (surfacePhaseChart q₂ e₂).source)
    (hcross : covectorDet
      (phaseDerivative (phi₁ ∘ (coordinateChart q).symm) (coordinateChart q p))
      (phaseDerivative (phi₂ ∘ (coordinateChart q).symm) (coordinateChart q p)) ≠ 0) :
    (fderiv ℝ (surfacePhaseTransition q₁ e₁ q₂ e₂) (surfacePhaseChart q₁ e₁ p) dy).1 ≠ 0 := by
  apply phase_crossing_first_nonzero q q₁ q₂
    (OpenPartialHomeomorph.refl JetPolynomial.Base) e₁ e₂
    contDiff_id contDiff_id he₁ hi₁ he₂
    (by rwa [surfacePhaseChart_refl_source]) h₁ h₂
  rw [surfacePhaseChart_refl_apply,
    phaseTransition_refl_covector q q₁ e₁ he₁ phi₁ hphi₁ hq h₁,
    phaseTransition_refl_covector q q₂ e₂ he₂ phi₂ hphi₂ hq h₂]
  exact hcross

end ClosedSurfaceR4

end

end OAI
