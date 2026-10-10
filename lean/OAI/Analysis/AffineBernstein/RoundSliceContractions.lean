import Mathlib
import OAI.Analysis.AffineBernstein.InverseTracePullback
import OAI.Analysis.AffineBernstein.RoundCofactorInverse

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] in
lemma dirDeriv_prod_right {g : S × E → ℝ} {s : S} {e : E}
    (hg : DifferentiableAt ℝ g (s,e)) (v : E) :
    dirDeriv v (fun y => g (s,y)) e = dirDeriv ((0:S),v) g (s,e) := by
  simpa using dirDeriv_affine_pullback (s,0) (ContinuousLinearMap.inr ℝ S E)
    (by simpa using hg) v

omit [CompleteSpace E] in
lemma flatInverseTrace_prod_right {g : S × E → ℝ} {s : S} {e : E}
    (hg : ContDiffAt ℝ ∞ g (s,e)) (A : Matrix κ κ ℝ) (v : κ → E) :
    flatInverseTrace A v (fun y => g (s,y)) e =
      flatInverseTrace A (fun i => ((0:S),v i)) g (s,e) := by
  simpa using flatInverseTrace_affine_pullback (s,0) (ContinuousLinearMap.inr ℝ S E)
    (by simpa using hg) A v

omit [CompleteSpace E] in
lemma flatInversePair_prod_right {f g : S × E → ℝ} {s : S} {e : E}
    (hf : DifferentiableAt ℝ f (s,e)) (hg : DifferentiableAt ℝ g (s,e))
    (A : Matrix κ κ ℝ) (v : κ → E) :
    flatInversePair A v (fun y => f (s,y)) (fun y => g (s,y)) e =
      flatInversePair A (fun i => ((0:S),v i)) f g (s,e) := by
  simpa using flatInversePair_affine_pullback (s,0) (ContinuousLinearMap.inr ℝ S E)
    (by simpa using hf) (by simpa using hg) A v

lemma supportNewtonTrace_slice (b c : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {H g : S × E → ℝ} {s : S} {e : E} (hH : ContDiffAt ℝ ∞ H (s,e))
    (hc : c (Sum.inr ()) = e)
    (hr : ∀ v, fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,e) = 0)
    (hR : (tubeRadiusMatrix H (s,e) c).det ≠ 0)
    (hg : ContDiffAt ℝ ∞ g (s,e)) (hgr : fderiv ℝ g (s,e) (0,e) = 0) :
    roundHessianContraction b (supportNewtonTensor b (fun y => H (s,y)))
      (fun y => g (s,y)) e =
      (tubeRadiusMatrix H (s,e) c).det *
        flatInverseTrace (tubeRadiusMatrix H (s,e) c) (fun i => ((0:S),c (Sum.inl i))) g (s,e) := by
  have hsH : ContDiffAt ℝ ∞ (fun y => H (s,y)) e := hH.comp e (contDiffAt_const.prodMk contDiffAt_id)
  have hsg : ContDiffAt ℝ ∞ (fun y => g (s,y)) e := hg.comp e (contDiffAt_const.prodMk contDiffAt_id)
  have hmat : (Matrix.of fun i j : κ => fderiv ℝ (fderiv ℝ (fun y => H (s,y))) e
      (c (Sum.inl i)) (c (Sum.inl j))) = tubeRadiusMatrix H (s,e) c := by
    ext i j
    exact second_fderiv_prod_right hH _ _
  have hrad (v : E) : fderiv ℝ (fderiv ℝ (fun y => H (s,y))) e v e = 0 := by
    rw [second_fderiv_prod_right hH,hr]
  have hgrad : fderiv ℝ (fun y => g (s,y)) e e = 0 := by
    change dirDeriv e (fun y => g (s,y)) e = 0
    rw [dirDeriv_prod_right (hg.differentiableAt (by simp))]
    exact hgr
  have hh := supportNewtonTrace_eq_inverse b c hsH hc hrad (by simpa only [hmat] using hR) hsg hgrad
  dsimp only at hh
  rw [hmat,flatInverseTrace_prod_right hg] at hh
  exact hh

lemma supportNewtonPair_slice (b c : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {H f g : S × E → ℝ} {s : S} {e : E} (hH : ContDiffAt ℝ ∞ H (s,e))
    (hc : c (Sum.inr ()) = e)
    (hr : ∀ v, fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,e) = 0)
    (hR : (tubeRadiusMatrix H (s,e) c).det ≠ 0)
    (hf : DifferentiableAt ℝ f (s,e)) (hg : DifferentiableAt ℝ g (s,e)) :
    supportNewtonTensor b (fun y => H (s,y)) e
      (tangentProjection e (gradient (fun y => f (s,y)) e))
      (tangentProjection e (gradient (fun y => g (s,y)) e)) =
      (tubeRadiusMatrix H (s,e) c).det *
        flatInversePair (tubeRadiusMatrix H (s,e) c) (fun i => ((0:S),c (Sum.inl i))) f g (s,e) := by
  have hsH : ContDiffAt ℝ ∞ (fun y => H (s,y)) e := hH.comp e (contDiffAt_const.prodMk contDiffAt_id)
  have hmat : (Matrix.of fun i j : κ => fderiv ℝ (fderiv ℝ (fun y => H (s,y))) e
      (c (Sum.inl i)) (c (Sum.inl j))) = tubeRadiusMatrix H (s,e) c := by
    ext i j
    exact second_fderiv_prod_right hH _ _
  have hrad (v : E) : fderiv ℝ (fderiv ℝ (fun y => H (s,y))) e v e = 0 := by
    rw [second_fderiv_prod_right hH,hr]
  have hh := supportNewtonPair_eq_inverse b c hsH hc hrad (by simpa only [hmat] using hR)
    (fun y => f (s,y)) (fun y => g (s,y))
  dsimp only at hh
  rw [hmat,flatInversePair_prod_right hf hg] at hh
  exact hh

end AffineBernstein
end

end OAI
