import OAI.Geometry.Convex.GeneralMahler.Linear.Gauss

namespace OAI
/-! Joint eigenbasis and transfer of diagonality to projection.
Allows a nonorthogonal eigenbasis too. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Module
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Function
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma cfc_eig_all {A:Mat m} (ha:A.IsHermitian) {x:Rn m} {c:ℝ} (hc:op A x=c • x)
    (f:ℝ→ℝ) : op (cfc f A) x=f c • x := by
  let b:=ha.eigenvectorBasis
  apply b.repr.injective
  ext i
  rw [b.repr_apply_apply,b.repr_apply_apply]
  have he := op_iff_hermitian.mp ha (b i) x
  have h1 := op_iff_hermitian.mp (cfc_herm f A) (b i) x
  rw [hc,op_eigen ha] at he
  rw [cfc_eigen' f ha] at h1
  rw [← h1]
  simp only [real_inner_smul_left,real_inner_smul_right] at *
  change f _* ⟪b i,x⟫=_
  change _*⟪b i,x⟫=_ at he
  rcases eq_or_ne ⟪b i,x⟫ 0 with hz|hz
  · rw [hz]; ring
  rw [mul_right_cancel₀ hz he]

omit [NeZero m] in
lemma joint_exists (M:Fin m→Mat m) (h:∀ i,(M i).IsHermitian)
    (hh:∀ i j,cmu (M i) (M j)=0):
    ∃ b:Basis (Fin m) ℝ (Rn m),∀ j,∃ l:Fin m→ℝ,∀ i,op (M i) (b j)=l i • b j := by
  classical
  let T := fun i=> (op (M i)).toLinearMap
  let s : Set (Rn m) := {x| ∃ l:Fin m→ℝ,∀ i,op (M i) x=l i • x}
  have he : ⊤ ≤ Submodule.span ℝ s := by
    have hT (i) : (T i).IsSymmetric := op_iff_hermitian.mp (h i)
    have hC : Pairwise (Commute on T) := by
      intro i j _
      have h₁:= congrArg op (sub_eq_zero.mp (hh i j))
      rw [_root_.map_mul,_root_.map_mul] at h₁
      exact congrArg (fun x:Rn m→L[ℝ]Rn m=>x.toLinearMap) h₁
    rw [← LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hC]
    apply iSup_le
    intro l x hx
    apply Submodule.subset_span
    refine ⟨l,fun i=>?_⟩
    exact Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx i)
  let b:=Basis.ofSpan he
  let b₀ : Basis (Fin m) ℝ (Rn m) := (EuclideanSpace.basisFun _ _).toBasis
  let k:=b.indexEquiv b₀
  refine ⟨b.reindex k,fun i=>?_⟩
  apply Basis.ofSpan_subset he
  rw [Basis.reindex_apply]
  exact ⟨_,rfl⟩

def diagDeriv (C: ProperCone ℝ (Rn m)) (b:Basis (Fin m) ℝ (Rn m)) :=
  ∀ᵐ x:Rn m,∀ j:Fin m,∃ l:ℝ, fderiv ℝ (coneProj C) x (b j) = l • b j

omit [NeZero m] in
lemma tendsto_aff_vol (B : Rn m ≃L[ℝ] Rn m) (a : Rn m):
    Tendsto (affineN B a) (ae volume) (ae volume) :=
  (tendsto_ae_affineN B a).mono_left ac_normal.ae_le

namespace ProjField
variable (q:ProjField m)
lemma projD (hm:∀ i j,cmu (q.M i) (q.M j)=0)
    (hz:∃ z:ℝ,∀ᵐ x∂normal m,q.Pmat z x=q.FL.Θ z x):
    ∃ b:Basis (Fin m) ℝ (Rn m),diagDeriv q.C b := by
  obtain ⟨b,hb⟩:=joint_exists q.M q.M_sym hm
  obtain ⟨z,hz⟩:=hz
  let F := affineN q.root (q.shift z)
  have he : ∀ᵐ x:Rn m,q.Pmat z x=q.FL.Θ z x := ac_normal.ae_le hz
  let G:=affineN q.root.symm (-(q.root.symm (q.shift z)))
  have hi : Tendsto G (ae volume) (ae volume) := tendsto_aff_vol ..
  refine ⟨b,?_⟩
  unfold diagDeriv
  filter_upwards [hi.eventually he] with x hx
  have hG : F (G x) = x := by simp [F,G,affineN]
  have hP : op (q.FL.Θ z (G x)) = fderiv ℝ (coneProj q.C) x := by
    rw [← hx]
    change op (op.symm (fderiv ℝ _ (F (G x))))=_
    rw [hG]; simp
  rw [← hP]
  intro j
  obtain ⟨l,hj⟩:=hb j
  let c:=∑ i:Fin m,(G x i)*l i
  have hl : op (q.Lmat (G x)) (b j)=c • b j := by
    unfold Lmat c
    simp_rw [_root_.map_sum,_root_.sum_apply,_root_.map_smul,_root_.smul_apply,hj]
    rw [Finset.sum_smul]; simp only [smul_smul]
  exact ⟨jump z c,cfc_eig_all (q.L_sym _) hl _⟩
end ProjField
end GeneralMahler

end

end OAI
