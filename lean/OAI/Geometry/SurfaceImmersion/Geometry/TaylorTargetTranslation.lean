import OAI.Geometry.SurfaceImmersion.Geometry.CenteredTaylorJets

namespace OAI

/-! Target translations preserve the prepared Taylor polynomial and its
crosscap direction map. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma surfaceTaylorTwo_add_const (f : Base → ProjectionTarget 3) (c : ProjectionTarget 3) :
    surfaceTaylorTwo (fun x => f x+c) = fun x => surfaceTaylorTwo f x+c := by
  have hd : fderiv ℝ (fun x => f x+c) = fderiv ℝ f := funext fun x => fderiv_add_const c
  funext x
  simp only [surfaceTaylorTwo,hd]
  abel

lemma centeredSurfaceTaylor_add_const (f : Base → ProjectionTarget 3) (a : Base)
    (c : ProjectionTarget 3) :
    centeredSurfaceTaylor (fun x => f x+c) a = fun x => centeredSurfaceTaylor f a x+c := by
  have ht : translatedSurface (fun x => f x+c) a = fun x => translatedSurface f a x+c := rfl
  funext x
  simp only [centeredSurfaceTaylor,ht,surfaceTaylorTwo_add_const]

lemma surfaceDirection_add_const (f : Base → ProjectionTarget 3) (b : Bool)
    (c : ProjectionTarget 3) : surfaceDirection (fun x => f x+c) b = surfaceDirection f b := by
  funext z
  simp only [surfaceDirection,fderiv_add_const]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
