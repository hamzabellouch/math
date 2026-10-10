import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
section LpProductJets
variable {E F A B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
def lpProductLinearMap (f : E →L[ℝ] A) (g : F →L[ℝ] B) :
    WithLp 2 (E×F) →L[ℝ] WithLp 2 (A×B) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.toContinuousLinearMap.comp
    ((f.prodMap g).comp (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap)
@[simp] lemma lpProductLinearMap_apply (f : E →L[ℝ] A) (g : F →L[ℝ] B)
    (x : WithLp 2 (E×F)) :
    lpProductLinearMap f g x = WithLp.toLp 2 (f x.fst,g x.snd) := rfl

def lpProductFunction (f : E → A) (g : F → B) (x : WithLp 2 (E×F)) :
    WithLp 2 (A×B) := WithLp.toLp 2 (f x.fst,g x.snd)
lemma lpProductFunction_hasFDerivAt {f : E → A} {g : F → B}
    {x : WithLp 2 (E×F)} {Df : E →L[ℝ] A} {Dg : F →L[ℝ] B}
    (hf : HasFDerivAt f Df x.fst) (hg : HasFDerivAt g Dg x.snd) :
    HasFDerivAt (lpProductFunction f g) (lpProductLinearMap Df Dg) x := by
  have hp := HasFDerivAt.prodMap (x.fst,x.snd) hf hg
  have hi := hp.comp x (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap.hasFDerivAt
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.toContinuousLinearMap.hasFDerivAt.comp x hi
lemma lpProductFunction_fderiv {f : E → A} {g : F → B}
    {x : WithLp 2 (E×F)} (hf : DifferentiableAt ℝ f x.fst) (hg : DifferentiableAt ℝ g x.snd) :
    fderiv ℝ (lpProductFunction f g) x = lpProductLinearMap (fderiv ℝ f x.fst) (fderiv ℝ g x.snd) :=
  (lpProductFunction_hasFDerivAt hf.hasFDerivAt hg.hasFDerivAt).fderiv
lemma lpProductFunction_contDiff {f : E → A} {g : F → B}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (lpProductFunction f g) := by
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.contDiff.comp
    ((hf.prodMap hg).comp (WithLp.prodContinuousLinearEquiv 2 ℝ E F).contDiff)
end LpProductJets
variable {E F A B : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
def lpProductIsometry (f : E →ₗᵢ[ℝ] A) (g : F →ₗᵢ[ℝ] B) :
    WithLp 2 (E×F) →ₗᵢ[ℝ] WithLp 2 (A×B) :=
  (lpProductLinearMap f.toContinuousLinearMap g.toContinuousLinearMap).toLinearMap.isometryOfInner
    (by intro x y; simp [WithLp.prod_inner_apply])
@[simp] lemma lpProductIsometry_apply (f : E →ₗᵢ[ℝ] A) (g : F →ₗᵢ[ℝ] B)
    (x : WithLp 2 (E×F)) : lpProductIsometry f g x = WithLp.toLp 2 (f x.fst,g x.snd) := rfl
end YauCounterexamples
end

end OAI
