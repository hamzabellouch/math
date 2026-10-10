import Mathlib
import OAI.Analysis.BoundedHochschild.FiniteMoments

namespace OAI

/-! Centered sequences and unitary moments in tracial ultrapowers. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildUltrapower
open HochschildRigidity TracialUltrapower HochschildPatching
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1) (ω : Ultrafilter ℕ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))

def traceScalarSequence (a : ℕ →ᵇ M) : ℕ →ᵇ M :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight (1:M)).compLeftContinuousBounded ℕ
    ((HochschildTraceNorm.traceCLM τ).compLeftContinuousBounded ℕ a)
@[simp] lemma traceScalarSequence_apply (a : ℕ →ᵇ M) (n : ℕ) :
    traceScalarSequence τ a n=τ (a n) • (1:M) := rfl

lemma quotient_traceScalarSequence (a : ℕ →ᵇ M) :
    quotientHom τ h1 ω htr (traceScalarSequence τ a)=
      quotientTrace τ h1 ω htr (quotientHom τ h1 ω htr a) • (1:Ultrapower τ h1 ω htr) := by
  change quotientHom τ h1 ω htr (traceScalarSequence τ a)=sequenceTrace τ ω a • (1:Ultrapower τ h1 ω htr)
  rw [← map_one (quotientHom τ h1 ω htr),← map_smul]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change _ ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ)
  rw [mem_nullSubmodule]
  change Tendsto (fun j => ‖τ.toPreGNS (τ (a j) • (1:M)-sequenceTrace τ ω a • (1:M))‖) (ω : Filter ℕ) (nhds 0)
  have ht := ((tendsto_sequenceTrace τ h1 ω a).sub_const (sequenceTrace τ ω a)).norm
  have hnorm : ‖τ.toPreGNS (1:M)‖=1 := by
    rw [PositiveLinearMap.preGNS_norm_def]
    simp [h1]
  simpa only [← sub_smul,map_smul,norm_smul,hnorm,mul_one,sub_self,norm_zero] using ht

def centeredSequence (a : ℕ →ᵇ M) : ℕ →ᵇ M := a-traceScalarSequence τ a
@[simp] lemma centeredSequence_apply (a : ℕ →ᵇ M) (n : ℕ) :
    centeredSequence τ a n=a n-τ (a n) • (1:M) := rfl
lemma quotient_centeredSequence (a : ℕ →ᵇ M) :
    quotientHom τ h1 ω htr (centeredSequence τ a)=
      quotientHom τ h1 ω htr a -
        quotientTrace τ h1 ω htr (quotientHom τ h1 ω htr a) • (1:Ultrapower τ h1 ω htr) := by
  rw [centeredSequence,map_sub,quotient_traceScalarSequence]
include h1 in
lemma norm_centered_half (a : M) (ha : ‖a‖ ≤ 1) : ‖(1/2:ℂ) • (a-τ a • (1:M))‖ ≤ 1 := by
  have ht := (norm_trace_le τ h1 a).trans ((preGNS_norm_le τ h1 a).trans ha)
  have hone : ‖(1:M)‖ ≤ 1 := IsStarProjection.norm_le _ (IsStarProjection.one M)
  rw [norm_smul]
  have h2 : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [h2]
  have hs : ‖τ a • (1:M)‖ ≤ 1 := by
    rw [norm_smul]
    exact (mul_le_mul ht hone (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hh := (norm_sub_le a (τ a • (1:M))).trans (add_le_add ha hs)
  linarith
omit [StarOrderedRing M] in
include h1 in
lemma trace_centered_half (a : M) : τ ((1/2:ℂ) • (a-τ a • (1:M)))=0 := by
  simp only [map_smul,map_sub,h1,smul_eq_mul,mul_one,sub_self,mul_zero]

def unitarySequence (u : ℕ → unitary M) : unitary (ℕ →ᵇ M) :=
  ⟨boundedHom (fun n => zpowersHom (unitary M) (u n)) (Multiplicative.ofAdd 1),by
    constructor <;> ext n <;> simp [zpowersHom]⟩
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma unitarySequence_apply (u : ℕ → unitary M) (n : ℕ) :
    (unitarySequence u : ℕ →ᵇ M) n=(u n:M) := by simp [unitarySequence,zpowersHom]

def quotientUnitary (u : ℕ → unitary M) : unitary (Ultrapower τ h1 ω htr) :=
  Unitary.map { (quotientHom τ h1 ω htr).toMonoidHom with map_star' := fun a => map_star (quotientHom τ h1 ω htr) a } (unitarySequence u)
@[simp] lemma quotientUnitary_coe (u : ℕ → unitary M) :
    (quotientUnitary τ h1 ω htr u : Ultrapower τ h1 ω htr)=quotientHom τ h1 ω htr (unitarySequence u : ℕ →ᵇ M) := rfl

end HochschildUltrapower

 

 

open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildPatching
open HochschildComparison
variable {M A : Type*} [CStarAlgebra M] [CStarAlgebra A]
variable {I : Type*} {K : ℕ}

def mapUnitary (φ : M →⋆ₐ[ℂ] A) : unitary M →⋆* unitary A :=
  Unitary.map { φ.toMonoidHom with map_star' := fun a => map_star φ a }
@[simp] lemma mapUnitary_coe (φ : M →⋆ₐ[ℂ] A) (u : unitary M) :
    (mapUnitary φ u : A)=φ (u:M) := rfl
lemma mapUnitary_zpow (φ : M →⋆ₐ[ℂ] A) (u : unitary M) (k : ℤ) :
    ((mapUnitary φ u)^k : unitary A).val=φ ((u^k : unitary M):M) := by
  rw [← map_zpow]
  rfl

lemma unitary_power_eq (u : unitary M) (k : Bool × ℕ) :
    (asPartialUnitary u).power k=((u^signedExponent k : unitary M):M) := by
  dsimp only [PartialUnitary.power,signedExponent]
  split
  · rw [zpow_neg,show (k.2 : ℤ)+1=((k.2+1 : ℕ):ℤ) by simp,zpow_natCast,← Unitary.star_eq_inv,
      Unitary.coe_star,SubmonoidClass.coe_pow,star_pow]
    rfl
  · rw [show (k.2 : ℤ)+1=((k.2+1 : ℕ):ℤ) by simp,zpow_natCast,SubmonoidClass.coe_pow]
    rfl

lemma mixedEval_unitary_product (F : I → M) (u : unitary M) (a : Option I) (l : List (WordAtom I K)) :
    mixedEval F (asPartialUnitary u) a l=wordCoeff F a *
      (l.map (fun b => ((u^signedExponent (b.1.1,b.1.2.val) : unitary M):M)*wordCoeff F b.2)).prod := by
  unfold mixedEval
  congr 1
  induction l with
  | nil => rfl
  | cons b l ih =>
    change (asPartialUnitary u).power (b.1.1,b.1.2.val)*wordCoeff F b.2*
      wordProduct (asPartialUnitary u).power (evaluatedTail F l)=_
    rw [unitary_power_eq,ih]
    rfl

lemma wordCoeff_hom (φ : M →⋆ₐ[ℂ] A) (F : I → M) (a : Option I) :
    φ (wordCoeff F a)=wordCoeff (φ ∘ F) a := by cases a <;> simp [wordCoeff]
lemma mixedEval_hom (φ : M →⋆ₐ[ℂ] A) (F : I → M) (u : unitary M)
    (a : Option I) (l : List (WordAtom I K)) :
    φ (mixedEval F (asPartialUnitary u) a l)=
      mixedEval (φ ∘ F) (asPartialUnitary (mapUnitary φ u)) a l := by
  rw [mixedEval_unitary_product,mixedEval_unitary_product,map_mul,wordCoeff_hom,map_list_prod,List.map_map]
  congr 1
  congr 1
  apply List.map_congr_left
  intro b hb
  simp only [Function.comp_apply,map_mul,wordCoeff_hom,mapUnitary_zpow]

def evalSequence (n : ℕ) : (ℕ →ᵇ M) →⋆ₐ[ℂ] M where
  toFun a := a n
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl
@[simp] lemma evalSequence_apply (n : ℕ) (a : ℕ →ᵇ M) : evalSequence n a=a n := rfl
lemma eval_unitarySequence (u : ℕ → unitary M) (n : ℕ) :
    mapUnitary (evalSequence n) (HochschildUltrapower.unitarySequence u)=u n := by
  apply Subtype.ext
  change ((u n)^(1:ℤ) : unitary M).val=(u n:M)
  rw [zpow_one]
lemma mixedEval_sequence (F : I → (ℕ →ᵇ M)) (u : ℕ → unitary M)
    (a : Option I) (l : List (WordAtom I K)) (n : ℕ) :
    mixedEval F (asPartialUnitary (HochschildUltrapower.unitarySequence u)) a l n=
      mixedEval (fun i => F i n) (asPartialUnitary (u n)) a l := by
  have hh := mixedEval_hom (evalSequence n) F (HochschildUltrapower.unitarySequence u) a l
  rw [eval_unitarySequence] at hh
  exact hh
end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildUltrapower
open BoundedHochschild HochschildRigidity TracialUltrapower HochschildPatching HochschildComparison
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
include e in
 

theorem exists_quotient_unitary_moments
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (A : ℕ → (ℕ →ᵇ M)) (hA : ∀ i n, ‖A i n‖ ≤ 1) :
    ∃ u : ℕ → unitary M, ∀ m K N : ℕ, ∀ a : BoundedWord (Fin m) K N,
      admissibleTail a.2.val →
      quotientTrace τ h1 ω htr (mixedEval
        (fun i : Fin m => quotientHom τ h1 ω htr (A i.val) -
          quotientTrace τ h1 ω htr (quotientHom τ h1 ω htr (A i.val)) • 1)
        (asPartialUnitary (quotientUnitary τ h1 ω htr u)) a.1 a.2.val)=0 := by
  let F : ℕ → ℕ → M := fun n i => (1/2:ℂ) • (A i n-τ (A i n) • 1)
  obtain ⟨u,hu⟩ := exists_small_moment_sequence e τ hτ h1 htr hfaith hfactor hdiff F
    (fun n i => norm_centered_half τ h1 (A i n) (hA i n))
    (fun n i => trace_centered_half τ h1 (A i n))
  refine ⟨u,fun m K N a ha => ?_⟩
  let B : Fin m → (ℕ →ᵇ M) := fun i => (1/2:ℂ) • centeredSequence τ (A i.val)
  let x : ℕ →ᵇ M := mixedEval B (asPartialUnitary (unitarySequence u)) a.1 a.2.val
  have hx : sequenceTrace τ ω x=0 := by
    apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω x)
    have hh := (hu m K N a ha).mono_left hω
    convert hh using 1
    funext n
    change τ (mixedEval B (asPartialUnitary (unitarySequence u)) a.1 a.2.val n)=_
    rw [mixedEval_sequence]
    rfl
  let C : Fin m → Ultrapower τ h1 ω htr := fun i => quotientHom τ h1 ω htr (A i.val) -
    quotientTrace τ h1 ω htr (quotientHom τ h1 ω htr (A i.val)) • 1
  have hB : quotientHom τ h1 ω htr ∘ B = fun i => (1/2:ℂ) • C i := by
    funext i
    change quotientHom τ h1 ω htr ((1/2:ℂ) • centeredSequence τ (A i.val))=_
    rw [map_smul,quotient_centeredSequence]
  have hm : mapUnitary (quotientHom τ h1 ω htr) (unitarySequence u)=quotientUnitary τ h1 ω htr u := rfl
  have ht : quotientTrace τ h1 ω htr (quotientHom τ h1 ω htr x)=0 := hx
  change quotientTrace τ h1 ω htr (quotientHom τ h1 ω htr
    (mixedEval B (asPartialUnitary (unitarySequence u)) a.1 a.2.val))=0 at ht
  rw [mixedEval_hom,hB,hm,mixedEval_smul,map_smul,smul_eq_mul] at ht
  exact (mul_eq_zero.mp ht).resolve_left (pow_ne_zero _ (by norm_num))

end HochschildUltrapower

 

 

namespace HochschildPatching
variable {K : ℕ}
lemma exists_finite_reindex (a : Option ℕ) (l : List (WordAtom ℕ K)) :
    ∃ m : ℕ, ∃ f : ℕ → Fin m,
      (a.map f).map Fin.val=a ∧
      (l.map (mapAtom f id)).map (mapAtom Fin.val id)=l := by
  classical
  let s : Finset ℕ := (a.toList ++ l.flatMap (fun b => b.2.toList)).toFinset
  obtain ⟨m,hm⟩ := s.exists_nat_subset_range
  let f : ℕ → Fin (m+1) := fun i => if hi : i < m+1 then ⟨i,hi⟩ else ⟨0,Nat.zero_lt_succ m⟩
  have hf (i : ℕ) (hi : i ∈ s) : (f i).val=i := by
    have hh := Finset.mem_range.mp (hm hi)
    dsimp only [f]
    rw [dite_eq_left (Nat.lt_succ_of_lt hh)]
  refine ⟨m+1,f,?_,?_⟩
  · cases a with
    | none => rfl
    | some i =>
      have hi : i ∈ s := by simp [s]
      simpa using congrArg some (hf i hi)
  · rw [List.map_map]
    conv_rhs => rw [← List.map_id l]
    apply List.map_congr_left
    intro b hb
    rcases b with ⟨k,b⟩
    cases b with
    | none => rfl
    | some i =>
      have hi : i ∈ s := by
        simp only [s,List.mem_toFinset,List.mem_append,List.mem_flatMap]
        exact Or.inr ⟨(k,some i),hb,by simp⟩
      simp only [Function.comp_apply,mapAtom,id_eq,Option.map_some,hf i hi]

lemma all_finite_words {M : Type*} [CStarAlgebra M]
    (τ : M → ℂ) (F : ℕ → M) (u : unitary M)
    (hfinite : ∀ m K N : ℕ, ∀ a : BoundedWord (Fin m) K N,
      admissibleTail a.2.val → τ (mixedEval (F ∘ Fin.val) (asPartialUnitary u) a.1 a.2.val)=0)
    (K : ℕ) (a : Option ℕ) (l : List (WordAtom ℕ K)) (hl : admissibleTail l) :
    τ (mixedEval F (asPartialUnitary u) a l)=0 := by
  obtain ⟨m,f,ha,hll⟩ := exists_finite_reindex a l
  let a' : BoundedWord (Fin m) K l.length := (a.map f,⟨l.map (mapAtom f id),by simp⟩)
  have hh := hfinite m K l.length a' (admissibleTail_map f id l hl)
  change τ (mixedEval (F ∘ Fin.val) (asPartialUnitary u) (a.map f) (l.map (mapAtom f id)))=0 at hh
  rw [← mixedEval_map F Fin.val id (fun _ => rfl),ha,hll] at hh
  exact hh
end HochschildPatching

 

 

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildUltrapower
open BoundedHochschild HochschildRigidity TracialUltrapower HochschildPatching HochschildComparison
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
include e in
theorem exists_quotient_unitary_all_moments
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    {I : Type*} [Countable I] [Nonempty I]
    (A : I → (ℕ →ᵇ M)) (hA : ∀ i n, ‖A i n‖ ≤ 1) :
    ∃ u : ℕ → unitary M, ∀ K : ℕ, ∀ a : Option I, ∀ l : List (WordAtom I K),
      admissibleTail l →
      quotientTrace τ h1 ω htr (mixedEval
        (fun i => quotientHom τ h1 ω htr (A i) -
          quotientTrace τ h1 ω htr (quotientHom τ h1 ω htr (A i)) • 1)
        (asPartialUnitary (quotientUnitary τ h1 ω htr u)) a l)=0 := by
  classical
  let : Inhabited I := ⟨Classical.arbitrary I⟩
  let : Encodable I := Encodable.ofCountable I
  let f : ℕ → I := fun n => (Encodable.decode (α := I) n).getD default
  have hf (i : I) : f (Encodable.encode i)=i := by simp [f]
  obtain ⟨u,hu⟩ := exists_quotient_unitary_moments e τ hτ h1 htr hfaith hfactor hdiff ω hω
    (A ∘ f) (fun i n => hA (f i) n)
  refine ⟨u,fun K a l hl => ?_⟩
  let C : ℕ → Ultrapower τ h1 ω htr := fun n => quotientHom τ h1 ω htr (A (f n)) -
    quotientTrace τ h1 ω htr (quotientHom τ h1 ω htr (A (f n))) • 1
  have hz := all_finite_words (quotientTrace τ h1 ω htr) C
    (quotientUnitary τ h1 ω htr u) hu K (a.map Encodable.encode)
    (l.map (mapAtom Encodable.encode id)) (admissibleTail_map Encodable.encode id l hl)
  rw [mixedEval_map C Encodable.encode id (fun _ => rfl)] at hz
  have hc : C ∘ Encodable.encode = fun i => quotientHom τ h1 ω htr (A i) -
      quotientTrace τ h1 ω htr (quotientHom τ h1 ω htr (A i)) • 1 := by
    funext i
    simp only [Function.comp_apply,C,hf]
  rw [hc] at hz
  exact hz
end HochschildUltrapower
end

end OAI
