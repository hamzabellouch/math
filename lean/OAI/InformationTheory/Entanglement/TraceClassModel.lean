import OAI.InformationTheory.Entanglement.HilbertTraceDifference

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
open ContinuousLinearMap
namespace SecretKey
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*}

def traceClassSpace (b : HilbertBasis ι ℂ H) : Submodule ℂ (H →L[ℂ] H) :=
  Submodule.span ℂ {A | HasFinitePositiveTrace b A}
abbrev TraceClass (b : HilbertBasis ι ℂ H) := traceClassSpace b
lemma positive_diagonal_real {A : H →L[ℂ] H} (hA : 0≤A) (x : H) :
    inner ℂ x (A x)=((inner ℂ x (A x)).re : ℂ) := by
  have hp := (nonneg_iff_isPositive.mp hA).inner_nonneg_right x
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp hp).2.symm
lemma positive_complex_diagonal_summable (b : HilbertBasis ι ℂ H)
    {A : H →L[ℂ] H} (hA : HasFinitePositiveTrace b A) :
    Summable (fun i => inner ℂ (b i) (A (b i))) := by
  have hs := hA.2.hasSum.mapL Complex.ofRealCLM
  have hc : Summable (fun i => ((inner ℂ (b i) (A (b i))).re : ℂ)) := hs.summable
  exact hc.congr (fun i => (positive_diagonal_real hA.1 (b i)).symm)
lemma traceClass_diagonal_summable (b : HilbertBasis ι ℂ H)
    {A : H →L[ℂ] H} (hA : A∈traceClassSpace b) :
    Summable (fun i => inner ℂ (b i) (A (b i))) := by
  induction hA using Submodule.span_induction with
  | mem x hx => exact positive_complex_diagonal_summable b hx
  | zero => simp
  | add x y hx hy hx' hy' =>
    simpa only [add_apply,inner_add_right] using hx'.add hy'
  | smul c x hx hx' =>
    simpa only [smul_apply,inner_smul_right] using hx'.mul_left c
lemma traceClass_positive_iff (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] H) :
    (A∈traceClassSpace b ∧ 0≤A) ↔ HasFinitePositiveTrace b A := by
  constructor
  · rintro ⟨hm,hp⟩
    exact ⟨hp,((traceClass_diagonal_summable b hm).hasSum.mapL Complex.reCLM).summable⟩
  · intro h
    exact ⟨Submodule.subset_span h,h.1⟩

def traceClassTrace (b : HilbertBasis ι ℂ H) : TraceClass b →ₗ[ℂ] ℂ where
  toFun A := ∑' i, inner ℂ (b i) ((A : H →L[ℂ] H) (b i))
  map_add' A B := by
    simp only [Submodule.coe_add,add_apply,inner_add_right]
    exact (traceClass_diagonal_summable b A.property).tsum_add
      (traceClass_diagonal_summable b B.property)
  map_smul' c A := by
    simp only [Submodule.coe_smul,smul_apply,inner_smul_right,RingHom.id_apply,smul_eq_mul]
    exact tsum_mul_left
lemma traceClassTrace_re (b : HilbertBasis ι ℂ H) (A : TraceClass b) :
    (traceClassTrace b A).re=hilbertTrace b A := by
  exact ((traceClass_diagonal_summable b A.property).hasSum.mapL Complex.reCLM).tsum_eq.symm
lemma traceClassTrace_positive (b : HilbertBasis ι ℂ H) (A : TraceClass b)
    (hp : 0≤(A : H →L[ℂ] H)) : 0≤traceClassTrace b A := by
  exact tsum_nonneg (fun index => (nonneg_iff_isPositive.mp hp).inner_nonneg_right (b index))

def DensityOperator (b : HilbertBasis ι ℂ H) :=
  {A : TraceClass b // 0≤(A : H →L[ℂ] H) ∧ traceClassTrace b A=1}

def TraceBlockPositive (b : HilbertBasis ι ℂ H) {r : Type*} [Fintype r]
    (A : Matrix r r (TraceClass b)) : Prop :=
  ∀ x : r → H, 0≤∑ i, ∑ j, inner ℂ (x i) ((A i j : H →L[ℂ] H) (x j))
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {κ : Type*}

def TraceCP (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (F : TraceClass b →ₗ[ℂ] TraceClass c) : Prop :=
  ∀ r : Type, ∀ _ : Fintype r, ∀ A : Matrix r r (TraceClass b),
    TraceBlockPositive b A → TraceBlockPositive c (fun i j => F (A i j))

end SecretKey

end

end OAI
