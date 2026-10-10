import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.EigenOrder

namespace OAI

section

noncomputable section
open Set Filter Matrix
open scoped Topology

namespace WeakMTWTransport
section BilinearMatrix
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def bilinearMatrix (B:E →L[ℝ] E →L[ℝ] ℝ) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (bilinearOperator B).toLinearMap.toMatrix (stdOrthonormalBasis ℝ E).toBasis
    (stdOrthonormalBasis ℝ E).toBasis

lemma bilinearMatrix_det (B:E →L[ℝ] E →L[ℝ] ℝ) :
    (bilinearMatrix B).det=(bilinearOperator B).det := by
  exact LinearMap.det_toMatrix _ _

lemma bilinearMatrix_quad (B:E →L[ℝ] E →L[ℝ] ℝ)
    (v:Fin (Module.finrank ℝ E) → ℝ) :
    v ⬝ᵥ (bilinearMatrix B *ᵥ v)=
      B ((stdOrthonormalBasis ℝ E).toBasis.equivFun.symm v)
        ((stdOrthonormalBasis ℝ E).toBasis.equivFun.symm v) := by
  let b:=stdOrthonormalBasis ℝ E
  let w:=b.toBasis.equivFun.symm v
  have hv: (fun i=>b.repr w i)=v:=by
    change b.toBasis.equivFun (b.toBasis.equivFun.symm v)=v
    exact b.toBasis.equivFun.apply_symm_apply v
  have hm:bilinearMatrix B *ᵥ v=(fun i=>b.repr (bilinearOperator B w) i):=by
    rw [←hv]
    exact (bilinearOperator B).toLinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis w
  rw [hm]
  nth_rw 1 [←hv]
  have H:=b.repr.inner_map_map (bilinearOperator B w) w
  rw [bilinearOperator_inner] at H
  simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct_comm] using H

lemma bilinearMatrix_nonneg {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hs:∀d e,B d e=B e d) (hp:∀d,0 ≤ B d d) :
    (bilinearMatrix B).PosSemidef := by
  apply (LinearMap.posSemidef_toMatrix_iff (stdOrthonormalBasis ℝ E)).2
  exact (LinearMap.isPositive_iff _).2 ⟨bilinearOperator_symmetric hs,by
    intro d
    change 0 ≤ inner ℝ (bilinearOperator B d) d
    rw [bilinearOperator_inner]
    exact hp d⟩

lemma bilinear_positive_of_det_ne_zero {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hs:∀d e,B d e=B e d) (hp:∀d,0 ≤ B d d)
    (hd:(bilinearOperator B).det≠0) : ∀d,d≠0 → 0 < B d d := by
  have HM: (bilinearMatrix B).PosDef:=(bilinearMatrix_nonneg hs hp).posDef_iff_det_ne_zero.mpr
    (by rwa [bilinearMatrix_det])
  intro d hd0
  let b:=(stdOrthonormalBasis ℝ E).toBasis
  have hv:b.equivFun d≠0:=by
    intro H
    apply hd0
    exact b.equivFun.injective (by simpa only [map_zero] using H)
  have H:=HM.dotProduct_mulVec_pos hv
  simpa only [star_trivial,bilinearMatrix_quad,b,LinearEquiv.symm_apply_apply] using H

lemma bilinear_det_nonneg {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hs:∀d e,B d e=B e d) (hp:∀d,0 ≤ B d d) :
    0 ≤ (bilinearOperator B).det := by
  rw [←bilinearMatrix_det]
  exact (bilinearMatrix_nonneg hs hp).det_nonneg

lemma bilinearOperator_tendsto {ι:Type*} {l:Filter ι}
    {B:ι → E →L[ℝ] E →L[ℝ] ℝ} {B₀:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:Tendsto B l (𝓝 B₀)) :
    Tendsto (fun i=>bilinearOperator (B i)) l (𝓝 (bilinearOperator B₀)) := by
  have hc:Continuous (fun B:E →L[ℝ] E →L[ℝ] ℝ=>bilinearOperator B):=
    continuous_const.clm_comp continuous_id
  exact hc.continuousAt.tendsto.comp hB

lemma bilinear_det_tendsto {ι:Type*} {l:Filter ι}
    {B:ι → E →L[ℝ] E →L[ℝ] ℝ} {B₀:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:Tendsto B l (𝓝 B₀)) :
    Tendsto (fun i=>(bilinearOperator (B i)).det) l (𝓝 (bilinearOperator B₀).det) := by
  exact ContinuousLinearMap.continuous_det.continuousAt.tendsto.comp (bilinearOperator_tendsto hB)

end BilinearMatrix
end WeakMTWTransport

end
end

end OAI
