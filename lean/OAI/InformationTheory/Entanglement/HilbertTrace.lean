import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
open ContinuousLinearMap
namespace SecretKey
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι κ : Type*}

def hilbertTrace (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : ℝ :=
  ∑' i, (inner ℂ (b i) (T (b i))).re

def HasFinitePositiveTrace (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : Prop :=
  0≤T ∧ Summable (fun i => (inner ℂ (b i) (T (b i))).re)

omit [CompleteSpace H] in
lemma hilbert_parseval (b : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i => ‖inner ℂ (b i) x‖^2) (‖x‖^2) := by
  have h := (b.hasSum_inner_mul_inner x x).mapL Complex.reCLM
  convert h using 1
  · ext i
    simp only [Complex.reCLM_apply,← inner_conj_symm x,Complex.conj_mul',
      ← Complex.ofReal_pow,Complex.ofReal_re]
  · exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x)

lemma positive_diagonal_sqrt {T : H →L[ℂ] H} (hT : 0≤T) (x : H) :
    (inner ℂ x (T x)).re=‖(CFC.sqrt T) x‖^2 := by
  have hs : (CFC.sqrt T).IsPositive := nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  have he : inner ℂ (CFC.sqrt T x) (CFC.sqrt T x)=inner ℂ x (T x) := by
    rw [hs.inner_left_eq_inner_right]
    change inner ℂ x ((CFC.sqrt T*CFC.sqrt T) x)=_
    rw [CFC.sqrt_mul_sqrt_self T]
  exact congrArg Complex.re he.symm

omit [CompleteSpace H] in
lemma symmetric_finite_compression_trace
    (b : HilbertBasis ι ℂ H) (S : H →L[ℂ] H) (hS : S.IsSymmetric)
    (hi : Summable (fun i => ‖S (b i)‖^2))
    (v : κ → H) (hv : Orthonormal ℂ v) (s : Finset κ) :
    ∑ j ∈ s, ‖S (v j)‖^2 ≤ ∑' i, ‖S (b i)‖^2 := by
  have he (j : κ) :
      HasSum (fun i => ‖inner ℂ (v j) (S (b i))‖^2) (‖S (v j)‖^2) := by
    convert hilbert_parseval b (S (v j)) using 1
    ext i
    have h := hS (b i) (v j)
    change inner ℂ (S (b i)) (v j)=inner ℂ (b i) (S (v j)) at h
    rw [← h,norm_inner_symm]
  calc
    ∑ j ∈ s, ‖S (v j)‖^2 = ∑ j ∈ s, ∑' i, ‖inner ℂ (v j) (S (b i))‖^2 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (he j).tsum_eq.symm
    _ = ∑' i, ∑ j ∈ s, ‖inner ℂ (v j) (S (b i))‖^2 :=
      ((fun j (_ : j∈s) => (he j).summable) |> Summable.tsum_finsetSum).symm
    _ ≤ ∑' i, ‖S (b i)‖^2 := by
      apply Summable.tsum_le_tsum _ ((hasSum_sum (s := s) fun j _ => he j).summable) hi
      intro i
      exact hv.sum_inner_products_le (S (b i))

lemma positive_finite_compression_trace
    (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H} (hT : HasFinitePositiveTrace b T)
    (v : κ → H) (hv : Orthonormal ℂ v) (s : Finset κ) :
    ∑ j ∈ s, (inner ℂ (v j) (T (v j))).re ≤ hilbertTrace b T := by
  have hi : Summable (fun i => ‖CFC.sqrt T (b i)‖^2) := by
    simpa only [← positive_diagonal_sqrt hT.1] using hT.2
  have hs := symmetric_finite_compression_trace b (CFC.sqrt T)
    (nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)).isSymmetric hi v hv s
  simpa only [← positive_diagonal_sqrt hT.1,hilbertTrace] using hs

lemma positiveTrace_change_basis (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H)
    {T : H →L[ℂ] H} (hT : HasFinitePositiveTrace b T) :
    HasFinitePositiveTrace c T ∧ hilbertTrace c T=hilbertTrace b T := by
  have hc : HasFinitePositiveTrace c T := ⟨hT.1,summable_of_sum_le
    (fun j => (nonneg_iff_isPositive.mp hT.1).re_inner_nonneg_right _)
    (fun s => positive_finite_compression_trace b hT c c.orthonormal s)⟩
  refine ⟨hc,le_antisymm ?_ ?_⟩
  · exact Real.tsum_le_of_sum_le (fun j => (nonneg_iff_isPositive.mp hT.1).re_inner_nonneg_right _)
      (fun s => positive_finite_compression_trace b hT c c.orthonormal s)
  · exact Real.tsum_le_of_sum_le (fun j => (nonneg_iff_isPositive.mp hT.1).re_inner_nonneg_right _)
      (fun s => positive_finite_compression_trace c hc b b.orthonormal s)

omit [CompleteSpace H] in
lemma hilbertTrace_add (b : HilbertBasis ι ℂ H) (A B : H →L[ℂ] H)
    (hA : Summable (fun i => (inner ℂ (b i) (A (b i))).re))
    (hB : Summable (fun i => (inner ℂ (b i) (B (b i))).re)) :
    hilbertTrace b (A+B)=hilbertTrace b A+hilbertTrace b B := by
  simp only [hilbertTrace,add_apply,inner_add_right,Complex.add_re]
  exact hA.tsum_add hB
omit [CompleteSpace H] in
lemma hilbertTrace_sub (b : HilbertBasis ι ℂ H) (A B : H →L[ℂ] H)
    (hA : Summable (fun i => (inner ℂ (b i) (A (b i))).re))
    (hB : Summable (fun i => (inner ℂ (b i) (B (b i))).re)) :
    hilbertTrace b (A-B)=hilbertTrace b A-hilbertTrace b B := by
  simp only [hilbertTrace,sub_apply,inner_sub_right,Complex.sub_re]
  exact hA.tsum_sub hB
omit [CompleteSpace H] in
lemma finitePositiveTrace_of_le (b : HilbertBasis ι ℂ H)
    {A B : H →L[ℂ] H} (hB : HasFinitePositiveTrace b B) (hA : 0≤A) (hAB : A≤B) :
    HasFinitePositiveTrace b A := by
  refine ⟨hA,Summable.of_nonneg_of_le
    (fun i => (nonneg_iff_isPositive.mp hA).re_inner_nonneg_right _) ?_ hB.2⟩
  intro i
  have h := (nonneg_iff_isPositive.mp (sub_nonneg.mpr hAB)).re_inner_nonneg_right (b i)
  change 0≤Complex.re (inner ℂ (b i) ((B-A) (b i))) at h
  simpa only [sub_apply,inner_sub_right,Complex.sub_re,sub_nonneg] using h

def hilbertTraceNorm (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : ℝ :=
  hilbertTrace b (CFC.abs T)
def HermitianTraceClass (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : Prop :=
  IsSelfAdjoint T ∧ HasFinitePositiveTrace b (CFC.abs T)
lemma hermitian_parts_finite (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H}
    (hT : HermitianTraceClass b T) :
    HasFinitePositiveTrace b (posPart T) ∧ HasFinitePositiveTrace b (negPart T) := by
  have he : posPart T+negPart T=CFC.abs T := CFC.posPart_add_negPart T hT.1
  exact ⟨finitePositiveTrace_of_le b hT.2 (CFC.posPart_nonneg T)
    (he ▸ le_add_of_nonneg_right (CFC.negPart_nonneg T)),
    finitePositiveTrace_of_le b hT.2 (CFC.negPart_nonneg T)
    (he ▸ le_add_of_nonneg_left (CFC.posPart_nonneg T))⟩
lemma hilbertTraceNorm_jordan (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H}
    (hT : HermitianTraceClass b T) :
    hilbertTraceNorm b T=hilbertTrace b (posPart T)+hilbertTrace b (negPart T) := by
  obtain ⟨hp,hm⟩ := hermitian_parts_finite b hT
  rw [hilbertTraceNorm,← CFC.posPart_add_negPart T hT.1,hilbertTrace_add b _ _ hp.2 hm.2]

end SecretKey

end

end OAI
