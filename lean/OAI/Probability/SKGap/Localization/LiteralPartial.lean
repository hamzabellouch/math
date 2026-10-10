import Mathlib
import OAI.Probability.SKGap.Localization.LiteralInitialSystem
import OAI.Probability.SKGap.Stability.LocalImplicitNode

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}
lemma SmallBound.of_local_eq {U V : VectorFields n} {x : Spin n} {C : ℝ}
    (h : SmallBound V x C) (hx : U x=V x) (hf : ∀k,U (flip x k)=V (flip x k)) :
    SmallBound U x C := by
  refine ⟨h.nonneg,?_,?_⟩
  · simpa only [hx] using h.size
  · rw [derivativeMatrix_congr_on_flips U V x hx hf]
    exact h.derivative

lemma literalInitial_partial_small (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (hd : d≠0) {R T B : ℝ} (hT : 0≤T) (he : vectorNorm e≤1)
    (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T)
    (hW : SmallBound w x B)
    (hw : w x=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) x)
    (hwf : ∀k,w (flip x k)=(literalInitial J j d f z m a c r e).sourceOf 1 (fun _=>y) (flip x k)) :
    SmallBound ((literalInitial J j d f z m a c r e).implicitPartial y) x
      (B*ratioSmallBudget (.kernel phiExpr.dz) T+
        ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T) := by
  have hel:=initial_ratio_bound (.kernel phiExpr.dz) z a r x hT hD
  have hs:=(hel.small_product hW).add (initialP_small f z a r e x hT he ha haf hD)
  have H : SmallBound (fun v i=>logSlope (z v i) (r i) (a v)*w v i+initialP f z a r e v i) x
      (B*ratioSmallBudget (.kernel phiExpr.dz) T+
        ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T) := by
    convert! hs using 1
    ext v i
    rw [logSlope_ratio]
  exact H.of_local_eq (literalInitial_partial_source _ _ _ _ _ _ _ _ _ _ _ _ hd x hw)
    (fun k=>literalInitial_partial_source _ _ _ _ _ _ _ _ _ _ _ _ hd _ (hwf k))
end SKGapCutoff.Recipe

end
end

end OAI
