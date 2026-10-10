import OAI.InformationTheory.Entanglement.TraceClassModel

namespace OAI

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder
open ContinuousLinearMap UniformSpace
namespace SecretKey
variable {H K L M : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M]

abbrev HilbertTensor (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] := Completion (H ⊗[ℂ] K)
def hilbertTmul (x : H) (y : K) : HilbertTensor H K := ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : Completion _)
lemma hilbertTmul_inner (x x' : H) (y y' : K) :
    inner ℂ (hilbertTmul x y) (hilbertTmul x' y')=inner ℂ x x'*inner ℂ y y' := by
  exact Completion.inner_coe (x ⊗ₜ[ℂ] y) (x' ⊗ₜ[ℂ] y')
lemma hilbertTmul_continuous : Continuous (fun p : H×K => hilbertTmul p.1 p.2) := by
  exact (Completion.continuous_coe _).comp TensorProduct.continuous_tmul
variable {ι κ : Type*}
lemma tensor_basis_orthonormal (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K) :
    Orthonormal ℂ (fun p : ι×κ => hilbertTmul (b p.1) (c p.2)) := by
  exact (b.orthonormal.tmul c.orthonormal).comp_linearIsometry Completion.toComplₗᵢ
lemma tensor_basis_dense (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K) :
    ⊤≤(Submodule.span ℂ (Set.range (fun p : ι×κ => hilbertTmul (b p.1) (c p.2)))).topologicalClosure := by
  let S := (Submodule.span ℂ (Set.range (fun p : ι×κ => hilbertTmul (b p.1) (c p.2)))).topologicalClosure
  have hS : IsClosed (S : Set (HilbertTensor H K)) := Submodule.isClosed_topologicalClosure _
  have hbase (i : ι) (j : κ) : hilbertTmul (b i) (c j)∈S :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(i,j),rfl⟩)
  have hfirst (i : ι) (y : K) : hilbertTmul (b i) y∈S := by
    let F : K →L[ℂ] HilbertTensor H K := Completion.toComplL.comp (TensorProduct.mkL ℂ H K (b i))
    have hs := (c.hasSum_repr y).mapL F
    apply hS.mem_of_tendsto hs
    filter_upwards with t
    apply S.sum_mem
    intro j hj
    rw [map_smul]
    exact S.smul_mem (c.repr y j) (hbase i j)
  have hsecond (x : H) (y : K) : hilbertTmul x y∈S := by
    let F : H →L[ℂ] HilbertTensor H K := Completion.toComplL.comp ((TensorProduct.mkL ℂ H K).flip y)
    have hs := (b.hasSum_repr x).mapL F
    apply hS.mem_of_tendsto hs
    filter_upwards with t
    apply S.sum_mem
    intro i hi
    rw [map_smul]
    exact S.smul_mem (b.repr x i) (hfirst i y)
  intro z hz
  change z∈S
  refine Completion.induction_on z hS ?_
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul x y => exact hsecond x y
  | add x y hx hy => simpa only [Completion.coe_add] using S.add_mem hx hy
def tensorHilbertBasis (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K) :
    HilbertBasis (ι×κ) ℂ (HilbertTensor H K) :=
  HilbertBasis.mk (tensor_basis_orthonormal b c) (tensor_basis_dense b c)
@[simp] lemma tensorHilbertBasis_apply (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K) (p : ι×κ) :
    tensorHilbertBasis b c p=hilbertTmul (b p.1) (c p.2) := by
  simp [tensorHilbertBasis]
def hilbertTensorMap (A : H →L[ℂ] L) (B : K →L[ℂ] M) : HilbertTensor H K →L[ℂ] HilbertTensor L M :=
  (Completion.toComplL.comp (TensorProduct.mapL A B)).extend Completion.toComplL
@[simp] lemma hilbertTensorMap_tmul (A : H →L[ℂ] L) (B : K →L[ℂ] M) (x : H) (y : K) :
    hilbertTensorMap A B (hilbertTmul x y)=hilbertTmul (A x) (B y) := by
  exact ContinuousLinearMap.extend_eq _ Completion.denseRange_coe (Completion.isUniformInducing_coe _) _

lemma hilbertTensor_ext {F G : HilbertTensor H K →L[ℂ] L}
    (h : ∀ x y, F (hilbertTmul x y)=G (hilbertTmul x y)) : F=G := by
  ext z
  refine Completion.induction_on z (isClosed_eq F.continuous G.continuous) ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add x y hx hy => simp only [Completion.coe_add,map_add,hx,hy]
lemma hilbertTensorMap_comp (A : H →L[ℂ] L) (B : K →L[ℂ] M)
    (C : H →L[ℂ] H) (D : K →L[ℂ] K) :
    hilbertTensorMap (A.comp C) (B.comp D)=
      (hilbertTensorMap A B).comp (hilbertTensorMap C D) := by
  apply hilbertTensor_ext
  intro x y
  simp
lemma hilbertTensor_inner_ext (F G : HilbertTensor H K →L[ℂ] HilbertTensor L M)
    (h : ∀ x y u v, inner ℂ (hilbertTmul u v) (F (hilbertTmul x y))=
      inner ℂ (hilbertTmul u v) (G (hilbertTmul x y))) : F=G := by
  apply hilbertTensor_ext
  intro x y
  apply ext_inner_left ℂ
  intro z
  refine Completion.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul u v => exact h x y u v
  | add u v hu hv => simp only [Completion.coe_add,inner_add_left,hu,hv]
variable [CompleteSpace H] [CompleteSpace K] [CompleteSpace L] [CompleteSpace M]

lemma hilbertTensorMap_adjoint (A : H →L[ℂ] L) (B : K →L[ℂ] M) :
    (hilbertTensorMap A B).adjoint=hilbertTensorMap A.adjoint B.adjoint := by
  apply hilbertTensor_inner_ext
  intro x y u v
  rw [adjoint_inner_right,hilbertTensorMap_tmul,hilbertTensorMap_tmul,
    hilbertTmul_inner,hilbertTmul_inner,A.adjoint_inner_right,B.adjoint_inner_right]

end SecretKey

end

end OAI
