import OAI.InformationTheory.Entanglement.HilbertTensor

namespace OAI

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder
open ContinuousLinearMap UniformSpace
namespace SecretKey
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι κ : Type*}
lemma hilbertTensorMap_nonneg {A : H →L[ℂ] H} {B : K →L[ℂ] K} (hA : 0≤A) (hB : 0≤B) :
    0≤hilbertTensorMap A B := by
  have ha : (CFC.sqrt A).adjoint=CFC.sqrt A := by
    rw [← star_eq_adjoint]; exact (CFC.sqrt_nonneg A).isSelfAdjoint
  have hb : (CFC.sqrt B).adjoint=CFC.sqrt B := by
    rw [← star_eq_adjoint]; exact (CFC.sqrt_nonneg B).isSelfAdjoint
  have he : star (hilbertTensorMap (CFC.sqrt A) (CFC.sqrt B))*
      hilbertTensorMap (CFC.sqrt A) (CFC.sqrt B)=hilbertTensorMap A B := by
    rw [star_eq_adjoint,hilbertTensorMap_adjoint,ha,hb,mul_def,← hilbertTensorMap_comp,
      ← mul_def,← mul_def,CFC.sqrt_mul_sqrt_self A hA,CFC.sqrt_mul_sqrt_self B hB]
  rw [← he]
  exact star_mul_self_nonneg (hilbertTensorMap (CFC.sqrt A) (CFC.sqrt B))
omit [CompleteSpace H] [CompleteSpace K] in
lemma tensor_positive_diagonal (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    {A : H →L[ℂ] H} {B : K →L[ℂ] K} (hA : 0≤A) (hB : 0≤B) (p : ι×κ) :
    (inner ℂ (tensorHilbertBasis b c p) (hilbertTensorMap A B (tensorHilbertBasis b c p))).re=
      (inner ℂ (b p.1) (A (b p.1))).re*(inner ℂ (c p.2) (B (c p.2))).re := by
  rw [tensorHilbertBasis_apply,hilbertTensorMap_tmul,hilbertTmul_inner,
    positive_diagonal_real hA,positive_diagonal_real hB]
  simp
lemma tensor_positive_trace (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    {A : H →L[ℂ] H} {B : K →L[ℂ] K}
    (hA : HasFinitePositiveTrace b A) (hB : HasFinitePositiveTrace c B) :
    HasFinitePositiveTrace (tensorHilbertBasis b c) (hilbertTensorMap A B) ∧
      hilbertTrace (tensorHilbertBasis b c) (hilbertTensorMap A B)=hilbertTrace b A*hilbertTrace c B := by
  have hnA (i : ι) : 0≤(inner ℂ (b i) (A (b i))).re :=
    (nonneg_iff_isPositive.mp hA.1).re_inner_nonneg_right _
  have hnB (j : κ) : 0≤(inner ℂ (c j) (B (c j))).re :=
    (nonneg_iff_isPositive.mp hB.1).re_inner_nonneg_right _
  have hs := hA.2.mul_of_nonneg hB.2 hnA hnB
  refine ⟨⟨hilbertTensorMap_nonneg hA.1 hB.1,?_⟩,?_⟩
  · exact hs.congr (fun p => (tensor_positive_diagonal b c hA.1 hB.1 p).symm)
  · unfold hilbertTrace
    simp_rw [tensor_positive_diagonal b c hA.1 hB.1]
    exact (hA.2.tsum_mul_tsum hB.2 hs).symm
omit [CompleteSpace H] [CompleteSpace K] in
lemma hilbertTmul_add_left (x y : H) (z : K) :
    hilbertTmul (x+y) z=hilbertTmul x z+hilbertTmul y z := by
  simp only [hilbertTmul,TensorProduct.add_tmul,Completion.coe_add]
omit [CompleteSpace H] [CompleteSpace K] in
lemma hilbertTmul_add_right (x : H) (y z : K) :
    hilbertTmul x (y+z)=hilbertTmul x y+hilbertTmul x z := by
  simp only [hilbertTmul,TensorProduct.tmul_add,Completion.coe_add]
omit [CompleteSpace H] [CompleteSpace K] in
lemma hilbertTmul_smul_left (s : ℂ) (x : H) (y : K) :
    hilbertTmul (s • x) y=s • hilbertTmul x y := by
  simp only [hilbertTmul,← TensorProduct.smul_tmul',Completion.coe_smul]
omit [CompleteSpace H] [CompleteSpace K] in
lemma hilbertTmul_smul_right (s : ℂ) (x : H) (y : K) :
    hilbertTmul x (s • y)=s • hilbertTmul x y := by
  simp [hilbertTmul,TensorProduct.tmul_smul]
omit [CompleteSpace H] [CompleteSpace K] in
lemma hilbertTensorMap_add_left (A B : H →L[ℂ] H) (C : K →L[ℂ] K) :
    hilbertTensorMap (A+B) C=hilbertTensorMap A C+hilbertTensorMap B C := by
  apply hilbertTensor_ext
  intro x y
  simp [hilbertTmul_add_left]
omit [CompleteSpace H] [CompleteSpace K] in
lemma hilbertTensorMap_add_right (A : H →L[ℂ] H) (B C : K →L[ℂ] K) :
    hilbertTensorMap A (B+C)=hilbertTensorMap A B+hilbertTensorMap A C := by
  apply hilbertTensor_ext
  intro x y
  simp [hilbertTmul_add_right]
omit [CompleteSpace H] [CompleteSpace K] in
lemma hilbertTensorMap_smul_left (s : ℂ) (A : H →L[ℂ] H) (B : K →L[ℂ] K) :
    hilbertTensorMap (s • A) B=s • hilbertTensorMap A B := by
  apply hilbertTensor_ext
  intro x y
  simp [hilbertTmul_smul_left]
omit [CompleteSpace H] [CompleteSpace K] in
lemma hilbertTensorMap_smul_right (s : ℂ) (A : H →L[ℂ] H) (B : K →L[ℂ] K) :
    hilbertTensorMap A (s • B)=s • hilbertTensorMap A B := by
  apply hilbertTensor_ext
  intro x y
  simp [hilbertTmul_smul_right]
omit [CompleteSpace H] [CompleteSpace K] in
@[simp] lemma hilbertTensorMap_zero_left (B : K →L[ℂ] K) :
    hilbertTensorMap (0 : H →L[ℂ] H) B=0 := by
  apply hilbertTensor_ext
  intro x y
  rw [hilbertTensorMap_tmul]
  simp [hilbertTmul]
omit [CompleteSpace H] [CompleteSpace K] in
@[simp] lemma hilbertTensorMap_zero_right (A : H →L[ℂ] H) :
    hilbertTensorMap A (0 : K →L[ℂ] K)=0 := by
  apply hilbertTensor_ext
  intro x y
  rw [hilbertTensorMap_tmul]
  simp [hilbertTmul]
lemma tensor_traceClass_mem (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    {A : H →L[ℂ] H} {B : K →L[ℂ] K}
    (hA : A∈traceClassSpace b) (hB : B∈traceClassSpace c) :
    hilbertTensorMap A B∈traceClassSpace (tensorHilbertBasis b c) := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    induction hB using Submodule.span_induction with
    | mem B hB => exact Submodule.subset_span (tensor_positive_trace b c hA hB).1
    | zero => simp
    | add x y _ _ hx hy =>
      rw [hilbertTensorMap_add_right]; exact Submodule.add_mem _ hx hy
    | smul s x _ hx =>
      rw [hilbertTensorMap_smul_right]; exact Submodule.smul_mem _ s hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [hilbertTensorMap_add_left]; exact Submodule.add_mem _ hx hy
  | smul s x _ hx =>
    rw [hilbertTensorMap_smul_left]; exact Submodule.smul_mem _ s hx

def traceTensor (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (A : TraceClass b) (B : TraceClass c) : TraceClass (tensorHilbertBasis b c) :=
  ⟨hilbertTensorMap A.val B.val,tensor_traceClass_mem b c A.property B.property⟩
lemma traceTensor_trace (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (A : TraceClass b) (B : TraceClass c) :
    traceClassTrace (tensorHilbertBasis b c) (traceTensor b c A B)=
      traceClassTrace b A*traceClassTrace c B := by
  have hs := traceClass_diagonal_summable (tensorHilbertBasis b c) (traceTensor b c A B).property
  have he (p : ι×κ) : inner ℂ (tensorHilbertBasis b c p)
      ((traceTensor b c A B).val (tensorHilbertBasis b c p))=
      inner ℂ (b p.1) (A.val (b p.1))*inner ℂ (c p.2) (B.val (c p.2)) := by
    simp [traceTensor,hilbertTmul_inner]
  simp_rw [he] at hs
  change (∑' p, inner ℂ (tensorHilbertBasis b c p)
    ((traceTensor b c A B).val (tensorHilbertBasis b c p)))=_
  simp_rw [he]
  exact ((traceClass_diagonal_summable b A.property).hasSum.mul
    (traceClass_diagonal_summable c B.property).hasSum hs).tsum_eq

end SecretKey

end

end OAI
