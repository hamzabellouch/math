import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.LinearPowerDirectional
import OAI.Geometry.SmoothYau.Smoothness.LpProductLinearMap

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
variable {E F A B : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
lemma lpProductFunction_metric {f : E → A} {g : F → B}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x v w : WithLp 2 (E×F)) :
    inner ℝ (fderiv ℝ (lpProductFunction f g) x v) (fderiv ℝ (lpProductFunction f g) x w) =
      inner ℝ (fderiv ℝ f x.fst v.fst) (fderiv ℝ f x.fst w.fst) +
      inner ℝ (fderiv ℝ g x.snd v.snd) (fderiv ℝ g x.snd w.snd) := by
  rw [lpProductFunction_fderiv (hf.differentiable (by simp) _)
    (hg.differentiable (by simp) _)]
  simp [WithLp.prod_inner_apply]
lemma lpProductRoundChart_first (p : A) (q : B) (L : E →ₗᵢ[ℝ] A) (K : F →ₗᵢ[ℝ] B) :
    HasFDerivAt (lpProductFunction (roundChart p L) (roundChart q K))
      (lpProductIsometry L K).toContinuousLinearMap 0 := by
  exact lpProductFunction_hasFDerivAt (roundChart_first p L) (roundChart_first q K)
lemma lpProductRoundChart_metric_first (p : A) (q : B) (L : E →ₗᵢ[ℝ] A) (K : F →ₗᵢ[ℝ] B)
    (hL : ∀ w, inner ℝ p (L w) = 0) (hK : ∀ w, inner ℝ q (K w) = 0)
    (v w : WithLp 2 (E×F)) :
    HasFDerivAt (fun x => inner ℝ
      (fderiv ℝ (lpProductFunction (roundChart p L) (roundChart q K)) x v)
      (fderiv ℝ (lpProductFunction (roundChart p L) (roundChart q K)) x w))
      (0 : WithLp 2 (E×F) →L[ℝ] ℝ) 0 := by
  simp_rw [lpProductFunction_metric (roundChart_smooth _ _) (roundChart_smooth _ _)]
  have h₁ := (roundChart_metric_first p L hL v.fst w.fst).comp
    (0 : WithLp 2 (E×F)) (WithLp.fstL 2 ℝ E F).hasFDerivAt
  have h₂ := (roundChart_metric_first q K hK v.snd w.snd).comp
    (0 : WithLp 2 (E×F)) (WithLp.sndL 2 ℝ E F).hasFDerivAt
  convert h₁.add h₂ using 1 <;> try rfl
  ext x
  simp
end YauCounterexamples
end

end OAI
