import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearMatrix
import OAI.Analysis.BiholderTransport.Regularity.FunctionalDet

namespace OAI

section

noncomputable section
open Matrix
open scoped MatrixOrder

namespace WeakMTWTransport
section BilinearDet
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma bilinearMatrix_apply (B:E →L[ℝ] E →L[ℝ] ℝ) (i j:Fin (Module.finrank ℝ E)) :
    bilinearMatrix B i j=B (stdOrthonormalBasis ℝ E j) (stdOrthonormalBasis ℝ E i) := by
  simp only [bilinearMatrix,LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis,OrthonormalBasis.repr_apply_apply]
  change inner ℝ (stdOrthonormalBasis ℝ E i) (bilinearOperator B (stdOrthonormalBasis ℝ E j)) = _
  rw [real_inner_comm,bilinearOperator_inner]

lemma functional_coords_dot (f:E →L[ℝ] ℝ) (d:E) :
    (fun i=>f (stdOrthonormalBasis ℝ E i)) ⬝ᵥ (stdOrthonormalBasis ℝ E).toBasis.equivFun d=f d := by
  have H:=congrArg f ((stdOrthonormalBasis ℝ E).toBasis.sum_repr d)
  simpa only [map_sum,map_smul,smul_eq_mul,mul_comm,dotProduct,OrthonormalBasis.coe_toBasis,
    Module.Basis.equivFun_apply] using H

lemma bilinearMatrix_symmetric {B:E →L[ℝ] E →L[ℝ] ℝ} (hs:∀d e,B d e=B e d) :
    (bilinearMatrix B).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial,bilinearMatrix_apply,hs]

lemma bilinearMatrix_positive {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hs:∀d e,B d e=B e d) (hp:∀d,d≠0 → 0 < B d d) :
    (bilinearMatrix B).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨bilinearMatrix_symmetric hs,?_⟩
  intro v hv
  simp only [star_trivial,bilinearMatrix_quad]
  apply hp
  intro H
  apply hv
  exact (stdOrthonormalBasis ℝ E).toBasis.equivFun.symm.injective (by simpa only [map_zero] using H)

lemma bilinearMatrix_le {A B:E →L[ℝ] E →L[ℝ] ℝ}
    (ha:∀d e,A d e=A e d) (hb:∀d e,B d e=B e d)
    (h:∀d,A d d≤B d d) : bilinearMatrix A≤bilinearMatrix B := by
  rw [Matrix.le_iff]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨(bilinearMatrix_symmetric hb).sub
    (bilinearMatrix_symmetric ha),?_⟩
  intro d
  simpa only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,bilinearMatrix_quad,sub_nonneg] using
    h ((stdOrthonormalBasis ℝ E).toBasis.equivFun.symm d)

lemma bilinearMatrix_rank_add (L:E →L[ℝ] E →L[ℝ] ℝ) (f:E →L[ℝ] ℝ) (m β:ℝ) :
    bilinearMatrix (m • L+β • f.smulRight f)=m • bilinearMatrix L+
      β • Matrix.vecMulVec (fun i=>f (stdOrthonormalBasis ℝ E i)) (fun i=>f (stdOrthonormalBasis ℝ E i)) := by
  ext i j
  simp only [bilinearMatrix_apply,_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,Matrix.add_apply,Matrix.smul_apply,Matrix.vecMulVec_apply]
  ring

lemma bilinear_determinant_gain [Nontrivial E]
    {L V W:E →L[ℝ] E →L[ℝ] ℝ} {f g:E →L[ℝ] ℝ} {e:E} {m β γ:ℝ}
    (hLs:∀d e,L d e=L e d) (hVs:∀d e,V d e=V e d) (hWs:∀d e,W d e=W e d)
    (hker:∀d,L e d=0) (hf:0 < f e) (hg:f e≤g e)
    (hm:0 < m) (hβ:0 < β) (hγ:0 < γ) (hV:∀d,d≠0 → 0 < V d d)
    (hVL:∀d,V d d≤L d d+β*(f d)^2)
    (hLW:∀d,m*L d d+γ*(g d)^2≤W d d) :
    γ*m^(Module.finrank ℝ E-1)*(bilinearOperator V).det≤β*(bilinearOperator W).det := by
  classical
  let b:=(stdOrthonormalBasis ℝ E).toBasis
  let : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp (Module.finrank_pos (R:=ℝ))
  have hLe:bilinearOperator L e=0:=by
    apply ext_inner_right ℝ
    intro d
    simp only [bilinearOperator_inner,hker,inner_zero_left]
  have hMe:bilinearMatrix L *ᵥ b.equivFun e=0:=by
    change (bilinearOperator L).toLinearMap.toMatrix b b *ᵥ b.equivFun e=0
    rw [Module.Basis.equivFun_apply,(bilinearOperator L).toLinearMap.toMatrix_mulVec_repr b b e]
    change (fun i => b.repr (bilinearOperator L e) i) = 0
    rw [hLe,map_zero]
    rfl
  have hfl:=functional_coords_dot f e
  have hgl:=functional_coords_dot g e
  have hF:∀d e,(L+β • f.smulRight f) d e=(L+β • f.smulRight f) e d:=by
    intro d e
    simp only [_root_.add_apply,_root_.smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul,hLs]
    ring
  have hG:∀d e,(m • L+γ • g.smulRight g) d e=(m • L+γ • g.smulRight g) e d:=by
    intro d e
    simp only [_root_.add_apply,_root_.smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul,hLs]
    ring
  have hVL':bilinearMatrix V≤bilinearMatrix L+β • Matrix.vecMulVec
      (fun i=>f (stdOrthonormalBasis ℝ E i)) (fun i=>f (stdOrthonormalBasis ℝ E i)):=by
    have H:=bilinearMatrix_le hVs hF (fun d=>by
      simpa only [_root_.add_apply,_root_.smul_apply,
        ContinuousLinearMap.smulRight_apply,smul_eq_mul,pow_two] using hVL d)
    have hr:=bilinearMatrix_rank_add L f 1 β
    simp only [one_smul] at hr
    rwa [hr] at H
  have hLW':m • bilinearMatrix L+γ • Matrix.vecMulVec
      (fun i=>g (stdOrthonormalBasis ℝ E i)) (fun i=>g (stdOrthonormalBasis ℝ E i))≤bilinearMatrix W:=by
    rw [←bilinearMatrix_rank_add]
    apply bilinearMatrix_le hG hWs
    intro d
    simpa only [_root_.add_apply,_root_.smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul,pow_two] using hLW d
  have H:=determinant_gain_of_functional_bounds (bilinearMatrix_symmetric hLs) hMe
    (by rwa [hfl]) (by rwa [hfl,hgl]) hm hβ hγ (bilinearMatrix_positive hVs hV) hVL' hLW'
  simpa only [Fintype.card_fin,bilinearMatrix_det] using H
end BilinearDet
end WeakMTWTransport

end
end

end OAI
