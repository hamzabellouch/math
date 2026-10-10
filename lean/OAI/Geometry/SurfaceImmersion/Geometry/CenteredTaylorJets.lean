import OAI.Geometry.SurfaceImmersion.Whitney.CenteredCrosscapPreparation

namespace OAI

/-! Centered Taylor preparation retains the complete second jet, hence
also the actual regular zero of the derivative-direction map. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma centeredSurfaceTaylor_smooth (f : Base → ProjectionTarget 3) (a : Base) :
    ContDiff ℝ ∞ (centeredSurfaceTaylor f a) :=
  (surfaceTaylorTwo_smooth _).comp (contDiff_id.sub contDiff_const)

lemma centeredSurfaceTaylor_fderiv {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a x : Base) :
    fderiv ℝ (centeredSurfaceTaylor f a) x =
      fderiv ℝ f a + fderiv ℝ (fderiv ℝ f) a (x-a) := by
  have htrans : ContDiff ℝ ∞ (translatedSurface f a) := hf.comp (contDiff_id.add contDiff_const)
  change fderiv ℝ (fun y => surfaceTaylorTwo (translatedSurface f a) (y-a)) x = _
  rw [fderiv_comp_sub,surfaceTaylorTwo_fderiv htrans]
  have hfirst : fderiv ℝ (translatedSurface f a) = fun y => fderiv ℝ f (y+a) := by
    funext y
    exact fderiv_comp_add_right a
  rw [hfirst,fderiv_comp_add_right]
  simp only [zero_add]

lemma centeredSurfaceTaylor_second {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a x : Base) :
    fderiv ℝ (fderiv ℝ (centeredSurfaceTaylor f a)) x = fderiv ℝ (fderiv ℝ f) a := by
  have he : fderiv ℝ (centeredSurfaceTaylor f a) =
      fun y => fderiv ℝ f a+fderiv ℝ (fderiv ℝ f) a (y-a) :=
    funext (centeredSurfaceTaylor_fderiv hf a)
  rw [he]
  exact ((fderiv ℝ (fderiv ℝ f) a).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const a) |>.const_add (fderiv ℝ f a)).fderiv

lemma surfaceDirection_congr_twoJet {f g : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (b : Bool) (z : Base × ℝ)
    (hfirst : fderiv ℝ f z.1 = fderiv ℝ g z.1)
    (hsecond : fderiv ℝ (fderiv ℝ f) z.1 = fderiv ℝ (fderiv ℝ g) z.1) :
    surfaceDirection f b z = surfaceDirection g b z ∧
      fderiv ℝ (surfaceDirection f b) z = fderiv ℝ (surfaceDirection g b) z := by
  constructor
  · simp only [surfaceDirection,hfirst]
  · rw [(surfaceDirection_hasFDerivAt hf b z).fderiv,
      (surfaceDirection_hasFDerivAt hg b z).fderiv]
    simp only [surfaceDirectionLinearization,hfirst,hsecond]

lemma centeredSurfaceTaylor_direction {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a : Base) (b : Bool) (t : ℝ) :
    surfaceDirection (centeredSurfaceTaylor f a) b (a,t) = surfaceDirection f b (a,t) ∧
      fderiv ℝ (surfaceDirection (centeredSurfaceTaylor f a) b) (a,t) =
        fderiv ℝ (surfaceDirection f b) (a,t) := by
  apply surfaceDirection_congr_twoJet (centeredSurfaceTaylor_smooth f a) hf
  · simpa only [Prod.fst,sub_self,map_zero,add_zero] using centeredSurfaceTaylor_fderiv hf a a
  · exact centeredSurfaceTaylor_second hf a a

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
