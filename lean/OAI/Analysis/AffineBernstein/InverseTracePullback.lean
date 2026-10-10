import Mathlib
import OAI.Analysis.AffineBernstein.FlatLogEuler

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma dirDeriv_affine_pullback {f : F → ℝ} (q₀ : F) (J : E →L[ℝ] F) {x : E}
    (hf : DifferentiableAt ℝ f (q₀+J x)) (v : E) :
    dirDeriv v (fun y => f (q₀+J y)) x = dirDeriv (J v) f (q₀+J x) := by
  change fderiv ℝ (fun y => f (q₀+J y)) x v = fderiv ℝ f (q₀+J x) (J v)
  exact congrArg (fun l : E →L[ℝ] ℝ => l v)
    ((hf.hasFDerivAt).comp x (J.hasFDerivAt.const_add q₀)).fderiv

lemma flatInverseTrace_affine_pullback {f : F → ℝ} (q₀ : F) (J : E →L[ℝ] F) {x : E}
    (hf : ContDiffAt ℝ ∞ f (q₀+J x)) (A : Matrix ι ι ℝ) (v : ι → E) :
    flatInverseTrace A v (fun y => f (q₀+J y)) x =
      flatInverseTrace A (fun i => J (v i)) f (q₀+J x) := by
  have hh : ContDiffAt ℝ ∞ (fun y => f (q₀+J y)) x :=
    hf.comp x (contDiffAt_const.add J.contDiff.contDiffAt)
  simp only [flatInverseTrace,dirDeriv_eq_second hh,dirDeriv_eq_second hf,
    second_fderiv_affine_comp J q₀ hf]

lemma flatInversePair_affine_pullback {f g : F → ℝ} (q₀ : F) (J : E →L[ℝ] F) {x : E}
    (hf : DifferentiableAt ℝ f (q₀+J x)) (hg : DifferentiableAt ℝ g (q₀+J x))
    (A : Matrix ι ι ℝ) (v : ι → E) :
    flatInversePair A v (fun y => f (q₀+J y)) (fun y => g (q₀+J y)) x =
      flatInversePair A (fun i => J (v i)) f g (q₀+J x) := by
  simp only [flatInversePair,dirDeriv_affine_pullback q₀ J hf,dirDeriv_affine_pullback q₀ J hg]

lemma flatInverseTrace_congr {f g : E → ℝ} {x : E} (hx : f =ᶠ[𝓝 x] g)
    (A : Matrix ι ι ℝ) (v : ι → E) : flatInverseTrace A v f x = flatInverseTrace A v g x := by
  simp only [flatInverseTrace,second_dirDeriv_congr hx]

lemma flatInversePair_congr {f f' g g' : E → ℝ} {x : E}
    (hf : f =ᶠ[𝓝 x] f') (hg : g =ᶠ[𝓝 x] g') (A : Matrix ι ι ℝ) (v : ι → E) :
    flatInversePair A v f g x = flatInversePair A v f' g' x := by
  simp only [flatInversePair,dirDeriv,hf.fderiv_eq,hg.fderiv_eq]

end AffineBernstein
end

end OAI
