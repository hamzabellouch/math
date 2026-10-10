import OAI.Geometry.SurfaceImmersion.Geometry.FlatSecondJetBounds

namespace OAI

/-! The actual second Taylor polynomial of a smooth surface map at the
coordinate origin, including exact vanishing jets of its remainder. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def surfaceQuadratic (B : Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3) (x : Base) :
    ProjectionTarget 3 := (1/2 : ℝ) • B x x

lemma surfaceQuadratic_smooth (B : Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3) :
    ContDiff ℝ ∞ (surfaceQuadratic B) :=
  (B.contDiff.clm_apply contDiff_id).const_smul _

lemma surfaceQuadratic_hasFDerivAt (B : Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3)
    (hB : ∀ v w, B v w = B w v) (x : Base) :
    HasFDerivAt (surfaceQuadratic B) (B x) x := by
  have hd := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)).const_smul (1/2 : ℝ)
  change HasFDerivAt (surfaceQuadratic B) _ x at hd
  convert hd using 1
  apply ContinuousLinearMap.ext
  intro v
  change B x v = (1/2 : ℝ) • (B x v+B v x)
  rw [hB v x]
  module

def surfaceTaylorTwo (f : Base → ProjectionTarget 3) (x : Base) : ProjectionTarget 3 :=
  f 0+fderiv ℝ f 0 x+surfaceQuadratic (fderiv ℝ (fderiv ℝ f) 0) x

lemma surfaceTaylorTwo_smooth (f : Base → ProjectionTarget 3) :
    ContDiff ℝ ∞ (surfaceTaylorTwo f) :=
  (contDiff_const.add (fderiv ℝ f 0).contDiff).add (surfaceQuadratic_smooth _)

lemma surfaceTaylorTwo_fderiv {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (x : Base) :
    fderiv ℝ (surfaceTaylorTwo f) x = fderiv ℝ f 0+fderiv ℝ (fderiv ℝ f) 0 x := by
  have hB : ∀ v w, fderiv ℝ (fderiv ℝ f) 0 v w = fderiv ℝ (fderiv ℝ f) 0 w v :=
    fun v w => hf.contDiffAt.isSymmSndFDerivAt (by simp) v w
  have hd := ((fderiv ℝ f 0).hasFDerivAt.const_add (f 0)).add
    (surfaceQuadratic_hasFDerivAt _ hB x)
  exact hd.fderiv

lemma surfaceTaylorTwo_second {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (x : Base) :
    fderiv ℝ (fderiv ℝ (surfaceTaylorTwo f)) x = fderiv ℝ (fderiv ℝ f) 0 := by
  have he : fderiv ℝ (surfaceTaylorTwo f) =
      fun y => fderiv ℝ f 0+fderiv ℝ (fderiv ℝ f) 0 y := funext (surfaceTaylorTwo_fderiv hf)
  rw [he]
  exact ((fderiv ℝ (fderiv ℝ f) 0).hasFDerivAt.const_add (fderiv ℝ f 0)).fderiv

lemma surfaceTaylorTwo_remainder_jets {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) :
    (f-surfaceTaylorTwo f) 0 = 0 ∧ fderiv ℝ (f-surfaceTaylorTwo f) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (f-surfaceTaylorTwo f)) 0 = 0 := by
  have hT := surfaceTaylorTwo_smooth f
  have hfirst : fderiv ℝ (f-surfaceTaylorTwo f) =
      fderiv ℝ f-fderiv ℝ (surfaceTaylorTwo f) := by
    funext x
    exact fderiv_sub (hf.differentiable (by simp) x) (hT.differentiable (by simp) x)
  refine ⟨?_,?_,?_⟩
  · simp [surfaceTaylorTwo,surfaceQuadratic]
  · rw [hfirst]
    simp [surfaceTaylorTwo_fderiv hf]
  · rw [hfirst,fderiv_sub
      ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) 0)
      ((hT.fderiv_right (m := ∞) (by simp)).differentiable (by simp) 0),
      surfaceTaylorTwo_second hf,sub_self]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
