import Mathlib
import OAI.Analysis.AffineBernstein.TubeInvariantSmooth
import OAI.Analysis.AffineBernstein.BilinearNewton
import OAI.Analysis.AffineBernstein.TensorFlux

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Partial fiber gradient, represented through the derivative of the joint scalar. -/
def jointAngularGradient (g : S × E → ℝ) (q : S × E) : E :=
  (InnerProductSpace.toDual ℝ E).symm ((fderiv ℝ g q).comp (ContinuousLinearMap.inr ℝ S E))

lemma jointAngularGradient_eq_slice {g : S × E → ℝ} {q : S × E}
    (hg : DifferentiableAt ℝ g q) :
    jointAngularGradient g q = gradient (fun y => g (q.1,y)) q.2 := by
  have hc : HasFDerivAt (fun y : E => (q.1,y)) (ContinuousLinearMap.inr ℝ S E) q.2 := by
    convert (hasFDerivAt_const (𝕜 := ℝ) q.1 q.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) q.2) using 1 <;> ext y <;> rfl
  have hd : HasFDerivAt (fun y => g (q.1,y))
      ((fderiv ℝ g q).comp (ContinuousLinearMap.inr ℝ S E)) q.2 := hg.hasFDerivAt.comp q.2 hc
  change (InnerProductSpace.toDual ℝ E).symm _ = (InnerProductSpace.toDual ℝ E).symm _
  rw [hd.fderiv]

lemma contDiffAt_jointAngularGradient {g : S × E → ℝ} {q : S × E}
    (hg : ContDiffAt ℝ ∞ g q) : ContDiffAt ℝ ∞ (jointAngularGradient g) q := by
  apply (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp q
  exact (hg.fderiv_right (m := ∞) (by simp)).clm_comp contDiffAt_const

/- Partial angular derivative of the gradient, represented without slice-dependent differentiation. -/
def jointAngularHessianVec (g : S × E → ℝ) (q : S × E) (v : E) : E :=
  (InnerProductSpace.toDual ℝ E).symm
    ((fderiv ℝ (fderiv ℝ g) q (0,v)).comp (ContinuousLinearMap.inr ℝ S E))

lemma jointAngularHessianVec_eq_slice {g : S × E → ℝ} {q : S × E}
    (hg : ContDiffAt ℝ ∞ g q) (v : E) :
    jointAngularHessianVec g q v = fderiv ℝ (gradient (fun y => g (q.1,y))) q.2 v := by
  apply ext_inner_right ℝ
  intro w
  have hs : ContDiffAt ℝ ∞ (fun y => g (q.1,y)) q.2 := hg.comp q.2 (contDiffAt_const.prodMk contDiffAt_id)
  rw [inner_fderiv_gradient hs,second_fderiv_prod_right (s := q.1) (e := q.2) hg]
  simp [jointAngularHessianVec]

lemma contDiffAt_jointAngularHessianVec {g : S × E → ℝ} {q : S × E}
    (hg : ContDiffAt ℝ ∞ g q) {v : S × E → E} (hv : ContDiffAt ℝ ∞ v q) :
    ContDiffAt ℝ ∞ (fun y => jointAngularHessianVec g y (v y)) q := by
  apply (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp q
  exact (((hg.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiffAt_const.prodMk hv)).clm_comp contDiffAt_const

def jointNewtonTensor (H : S × E → ℝ) (b : OrthonormalBasis ι ℝ E) (q : S × E) :
    E →L[ℝ] E →L[ℝ] ℝ := bilinearOfMatrix b (newtonTensor (tubeFullRadiusMatrix H q b))

lemma jointNewtonTensor_eq_slice {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    jointNewtonTensor H b q = supportNewtonTensor b (fun y => H (q.1,y)) q.2 := by
  unfold jointNewtonTensor supportNewtonTensor
  congr 2
  ext i j
  exact (second_fderiv_prod_right (s := q.1) (e := q.2) hH (b i) (b j)).symm

lemma contDiffAt_jointNewtonTensor {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContDiffAt ℝ ∞ (jointNewtonTensor H b) q := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @NormedSpace.toIsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) _ _ _
  unfold jointNewtonTensor bilinearOfMatrix
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    ((contDiff_newtonTensor_entry i j).contDiffAt.comp q (contDiffAt_tubeFullRadiusMatrix hH b)).smul contDiffAt_const

lemma continuousOn_sliceAngularGradient {U : Set (S × E)} {g : S × E → ℝ}
    (hg : ∀ q ∈ U, ContDiffAt ℝ ∞ g q) :
    ContinuousOn (fun q : S × E => gradient (fun y => g (q.1,y)) q.2) U := by
  have hc : ContinuousOn (jointAngularGradient g) U :=
    fun q hq => (contDiffAt_jointAngularGradient (hg q hq)).continuousAt.continuousWithinAt
  apply hc.congr
  intro q hq
  exact (jointAngularGradient_eq_slice ((hg q hq).differentiableAt (by simp))).symm

lemma continuousOn_sliceNewtonTensor {U : Set (S × E)} {H : S × E → ℝ}
    (hH : ∀ q ∈ U, ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContinuousOn (fun q : S × E => supportNewtonTensor b (fun y => H (q.1,y)) q.2) U := by
  have hc : ContinuousOn (jointNewtonTensor H b) U :=
    fun q hq => (contDiffAt_jointNewtonTensor (hH q hq) b).continuousAt.continuousWithinAt
  apply hc.congr
  intro q hq
  exact (jointNewtonTensor_eq_slice (hH q hq) b).symm

omit [CompleteSpace E] in
lemma contDiffAt_tangentProjection {v : S × E → E} {q : S × E}
    (hv : ContDiffAt ℝ ∞ v q) :
    ContDiffAt ℝ ∞ (fun y : S × E => tangentProjection y.2 (v y)) q :=
  hv.sub ((contDiffAt_snd.inner ℝ hv).smul contDiffAt_snd)

lemma continuousOn_sliceRoundContraction {U : Set (S × E)} {H g : S × E → ℝ}
    (hH : ∀ q ∈ U, ContDiffAt ℝ ∞ H q) (hg : ∀ q ∈ U, ContDiffAt ℝ ∞ g q)
    (b : OrthonormalBasis ι ℝ E) :
    ContinuousOn (fun q : S × E => roundHessianContraction b
      (supportNewtonTensor b (fun y => H (q.1,y))) (fun y => g (q.1,y)) q.2) U := by
  let t : S × E → ι → E := fun q i => tangentProjection q.2 (b i)
  let J : S × E → ℝ := fun q => ∑ i, jointNewtonTensor H b q (t q i)
    (tangentProjection q.2 (jointAngularHessianVec g q (t q i)) -
      inner ℝ q.2 (jointAngularGradient g q) • t q i)
  have hc : ContinuousOn J U := by
    intro q hq
    apply ContinuousAt.continuousWithinAt
    apply ContDiffAt.continuousAt (𝕜 := ℝ) (n := ∞)
    apply ContDiffAt.sum
    intro i _
    have ht : ContDiffAt ℝ ∞ (fun y => t y i) q := contDiffAt_tangentProjection contDiffAt_const
    exact ((contDiffAt_jointNewtonTensor (hH q hq) b).clm_apply ht).clm_apply
      ((contDiffAt_tangentProjection (contDiffAt_jointAngularHessianVec (hg q hq) ht)).sub
        ((contDiffAt_snd.inner ℝ (contDiffAt_jointAngularGradient (hg q hq))).smul ht))
  apply hc.congr
  intro q hq
  unfold J roundHessianContraction
  simp only [jointNewtonTensor_eq_slice (hH q hq) b,
    jointAngularGradient_eq_slice ((hg q hq).differentiableAt (by simp)),
    jointAngularHessianVec_eq_slice (hg q hq)]
  rfl

end AffineBernstein
end

end OAI
