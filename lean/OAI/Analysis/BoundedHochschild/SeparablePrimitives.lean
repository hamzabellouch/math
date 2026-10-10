import Mathlib
import OAI.Analysis.BoundedHochschild.FinitePaths
import OAI.Analysis.BoundedHochschild.TraceExpectations

namespace OAI

/-! Dense unitary bases, normal expectations and separable finite exactness. -/

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
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

lemma preGNS_sq_le_traceVector (b : M) :
    ‖τ.toPreGNS b‖^2 ≤ ‖b‖*‖traceVectorLinear e τ hL hτ b‖ := by
  have hs : ‖τ.toPreGNS b‖^2=‖τ (star b*b)‖ := by
    have hh := congrArg norm (τ.preGNS_norm_sq (τ.toPreGNS b))
    simpa only [norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),PositiveLinearMap.ofPreGNS_toPreGNS] using hh
  rw [hs]
  have hh := traceVector_spec e τ hL hτ b b
  calc
    _ = ‖e.symm b (traceVectorLinear e τ hL hτ b)‖ := by rw [traceVectorLinear_apply,hh,norm_star]
    _ ≤ ‖e.symm b‖*‖traceVectorLinear e τ hL hτ b‖ := (e.symm b).le_opNorm _
    _ = _ := by rw [e.symm.norm_map]

include hL hτ in
 

theorem exists_dense_unitary_base [TopologicalSpace.SeparableSpace X] :
    ∃ v : ℕ → unitary M, ∀ u : unitary M, ∃ j : ℕ → ℕ,
      Tendsto (fun k => ‖τ.toPreGNS ((v (j k):M)-(u:M))‖) atTop (𝓝 0) := by
  classical
  let J := traceVectorLinear e τ hL hτ
  let S : Set X := Set.range (fun u : unitary M => J (u:M))
  let : Nonempty S := ⟨⟨J (1:M),⟨1,rfl⟩⟩⟩
  let d : ℕ → S := TopologicalSpace.denseSeq S
  choose v hv using fun n => (d n).property
  refine ⟨v,fun u => ?_⟩
  let z : S := ⟨J (u:M),⟨u,rfl⟩⟩
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp
    ((TopologicalSpace.denseRange_denseSeq S) z)
  choose j hj using hy
  have hconv : Tendsto (fun k => J (v (j k):M)) atTop (𝓝 (J (u:M))) := by
    have ht := continuous_subtype_val.tendsto z |>.comp hyt
    have hf : (fun k => J (v (j k):M))=(fun k => (y k:X)) := by
      funext k
      have hh := congrArg Subtype.val (hj k)
      exact (hv (j k)).trans hh
    rw [hf]
    exact ht
  have hJn : Tendsto (fun k => ‖J ((v (j k):M)-(u:M))‖) atTop (𝓝 0) := by
    have hh := (hconv.sub_const (J (u:M))).norm
    simpa only [map_sub,sub_self,norm_zero] using hh
  have hunit (a : unitary M) : ‖(a:M)‖ ≤ 1 := by
    have hh := CStarRing.norm_coe_unitary_mul a (1:M)
    simp only [mul_one] at hh
    rw [hh]
    by_cases ht : Nontrivial M
    · let : Nontrivial M := ht
      exact (norm_one (α := M)).le
    · have : Subsingleton M := not_nontrivial_iff_subsingleton.mp ht
      simp [Subsingleton.elim (1:M) 0]
  have hbound (k : ℕ) : ‖τ.toPreGNS ((v (j k):M)-(u:M))‖^2 ≤
      2*‖J ((v (j k):M)-(u:M))‖ := by
    apply (preGNS_sq_le_traceVector e τ hL hτ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith [hunit (v (j k)),hunit u])
  have hsq : Tendsto (fun k => ‖τ.toPreGNS ((v (j k):M)-(u:M))‖^2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hbound (by simpa using hJn.const_mul 2)
  refine ⟨j,?_⟩
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hh

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildWalk HochschildRare
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [TopologicalSpace.SeparableSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

 

theorem primitive_of_separable_normal_finite_paths
    (h1 : τ 1=1) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (hτ : TraceInPredual e τ) (hpaths : FinitePathTests τ)
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0)
    (hnormal : ∀ a : Fin n → M, HasPreadjoint e (f.curryRight a)) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  obtain ⟨v,hv⟩ := exists_dense_unitary_base e τ hL hτ
  obtain ⟨label,hbase,htests⟩ := exists_label_of_finite_paths τ hpaths v
  refine primitive_of_normal_finite_tests e τ h1 htr hfaith hL hR hτ
    label htests ?_ f hf hnormal
  intro u
  obtain ⟨j,hj⟩ := hv u
  refine ⟨j,?_⟩
  simpa only [hbase] using hj

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

omit [StarOrderedRing M] in
 

lemma denseRange_traceVector (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) :
    DenseRange (traceVectorLinear e τ hL hτ) := by
  let J := traceVectorLinear e τ hL hτ
  let S := (LinearMap.range J).topologicalClosure
  let : IsClosed (S : Set X) := (LinearMap.range J).isClosed_topologicalClosure
  have hzero (f : StrongDual ℂ X) (hf : ∀ b : M, f (J b)=0) : f=0 := by
    have ha : e f=0 := by
      apply hfaith
      apply star_eq_zero.mp
      rw [← traceVector_spec e τ hL hτ (e f) (e f), e.symm_apply_apply]
      exact hf (e f)
    exact e.injective (ha.trans (map_zero e).symm)
  change Dense (Set.range J)
  rw [← LinearMap.coe_range]
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro z _
  apply (Submodule.Quotient.mk_eq_zero S).mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
  intro f
  have hf : f.comp S.mkQL=0 := by
    apply hzero
    intro b
    have hb : J b ∈ S := (LinearMap.range J).le_topologicalClosure ⟨b,rfl⟩
    have hh : (Submodule.Quotient.mk (p := S) (J b) : X ⧸ S)=0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr hb
    change f (Submodule.Quotient.mk (J b))=0
    rw [hh,map_zero]
  exact congrArg (fun F : StrongDual ℂ X => F z) hf

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M N X Y : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
variable (eM : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (eN : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N)
  (τM : M →ₚ[ℂ] ℂ) (τN : N →ₚ[ℂ] ℂ)
  (hLM : ∀ b : M, HasPreadjoint eM (ContinuousLinearMap.mul ℂ M b))
  (hLN : ∀ b : N, HasPreadjoint eN (ContinuousLinearMap.mul ℂ N b))
  (hτM : TraceInPredual eM τM) (hτN : TraceInPredual eN τN)

omit [StarOrderedRing M] [StarOrderedRing N] in
include hLM hLN hτM hτN in
 

theorem exists_preadjoint_of_trace_adjoint
    (hfaithN : ∀ a : N, τN (star a*a)=0 → a=0)
    (A : M →L[ℂ] N) (B : N →L[ℂ] M)
    (hadj : ∀ a b, τN (star b*A a)=τM (star (B b)*a)) :
    ∃ P : Y →L[ℂ] X, ‖P‖ ≤ ‖A‖ ∧
      ∀ a z, eN.symm (A a) z=eM.symm a (P z) := by
  let JM := traceVectorLinear eM τM hLM hτM
  let JN := traceVectorLinear eN τN hLN hτN
  let F := JM.comp B.toLinearMap
  have hd : DenseRange JN := denseRange_traceVector eN τN hLN hτN hfaithN
  have hb (b : N) : ‖F b‖ ≤ ‖A‖*‖JN b‖ := by
    apply NormedSpace.norm_le_dual_bound ℂ _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro f
    have hs : f (F b)=eN.symm (A (eM f)) (JN b) := by
      change f (traceVector eM τM hLM hτM (B b))=_
      have hs0 := traceVector_spec eM τM hLM hτM (B b) (eM f)
      simp only [eM.symm_apply_apply] at hs0
      rw [hs0]
      change _=eN.symm (A (eM f)) (traceVector eN τN hLN hτN b)
      rw [traceVector_spec,hadj]
    rw [hs]
    calc
      _ ≤ ‖eN.symm (A (eM f))‖*‖JN b‖ := (eN.symm (A (eM f))).le_opNorm _
      _ = ‖A (eM f)‖*‖JN b‖ := by rw [eN.symm.norm_map]
      _ ≤ (‖A‖*‖eM f‖)*‖JN b‖ := mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
      _ = (‖A‖*‖JN b‖)*‖f‖ := by rw [eM.norm_map]; ring
  let P : Y →L[ℂ] X := F.extendOfNorm JN
  refine ⟨P,LinearMap.opNorm_extendOfNorm_le hd (norm_nonneg _) hb,fun a z => ?_⟩
  have heq : (fun z => eN.symm (A a) z)=(fun z => eM.symm a (P z)) := by
    apply hd.equalizer (eN.symm (A a)).continuous ((eM.symm a).continuous.comp P.continuous)
    funext b
    change eN.symm (A a) (JN b)=eM.symm a (F.extendOfNorm JN (JN b))
    rw [LinearMap.extendOfNorm_eq hd ⟨‖A‖,hb⟩]
    change eN.symm (A a) (traceVector eN τN hLN hτN b)=
      eM.symm a (traceVector eM τM hLM hτM (B b))
    rw [traceVector_spec,traceVector_spec,hadj]
  exact congrFun heq z

omit [StarOrderedRing M] in
include hLM hτM in
 

lemma right_hasPreadjoint_of_left
    (hfaith : ∀ a : M, τM (star a*a)=0 → a=0)
    (htr : ∀ a b : M, τM (a*b)=τM (b*a))
    (b : M) : HasPreadjoint eM ((ContinuousLinearMap.mul ℂ M).flip b) := by
  obtain ⟨P,_,hP⟩ := exists_preadjoint_of_trace_adjoint eM eM τM τM hLM hLM hτM hτM
    hfaith ((ContinuousLinearMap.mul ℂ M).flip b)
    ((ContinuousLinearMap.mul ℂ M).flip (star b)) (by
      intro a c
      change τM (star c*(a*b))=τM (star (c*star b)*a)
      simp only [star_mul,star_star]
      rw [← mul_assoc,htr,mul_assoc])
  intro z
  exact ⟨P z,fun a => hP a z⟩

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M N X Y : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
variable (eM : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (eN : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N)
  (τM : M →ₚ[ℂ] ℂ) (τN : N →ₚ[ℂ] ℂ)

omit [StarOrderedRing M] [StarOrderedRing N] in
lemma trace_preserving_norm
    (hfaithN : ∀ a : N, τN (star a*a)=0 → a=0)
    (I : N →⋆ₐ[ℂ] M) (hp : ∀ b : N, τM (I b)=τN b) (b : N) :
    ‖I b‖=‖b‖ := by
  apply NonUnitalStarAlgHom.norm_map I
  intro a c hac
  apply sub_eq_zero.mp
  apply hfaithN
  rw [← hp,map_mul,map_star,map_sub,hac,sub_self,star_zero,zero_mul,map_zero]

 

theorem exists_normal_expected_embedding
    (htrM : ∀ a b : M, τM (a*b)=τM (b*a)) (htrN : ∀ a b : N, τN (a*b)=τN (b*a))
    (hLM : ∀ b : M, HasPreadjoint eM (ContinuousLinearMap.mul ℂ M b))
    (hLN : ∀ b : N, HasPreadjoint eN (ContinuousLinearMap.mul ℂ N b))
    (hτM : TraceInPredual eM τM) (hτN : TraceInPredual eN τN)
    (hfaithM : ∀ a : M, τM (star a*a)=0 → a=0)
    (hfaithN : ∀ a : N, τN (star a*a)=0 → a=0)
    (I : N →⋆ₐ[ℂ] M) (hp : ∀ b : N, τM (I b)=τN b) :
    ∃ E : ExpectedEmbedding N M, (∀ b : N, E.includeMap b=I b) ∧
      (∀ x : M, ∀ b : N, τN (star b*E.expectMap x)=τM (star (I b)*x)) ∧
      (∃ P : Y →L[ℂ] X, ‖P‖ ≤ 1 ∧ ∀ a z, eN.symm (E.expectMap a) z=eM.symm a (P z)) ∧
      (∃ Q : X →L[ℂ] Y, ‖Q‖ ≤ 1 ∧ ∀ a z, eM.symm (E.includeMap a) z=eN.symm a (Q z)) := by
  have hI := trace_preserving_norm τM τN hfaithN I hp
  obtain ⟨E,hEi,hE⟩ := exists_expected_embedding eN τN τM htrN htrM hLN hτN hfaithN I hp hI
  have hEn : ‖E.expectMap‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by simpa only [one_mul] using E.expect_norm x)
  have hIn : ‖E.includeMap‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by rw [one_mul,E.include_norm])
  obtain ⟨P,hPn,hP⟩ := exists_preadjoint_of_trace_adjoint eM eN τM τN
    hLM hLN hτM hτN hfaithN E.expectMap E.includeMap (by
      intro a b
      rw [hEi,hE])
  obtain ⟨Q,hQn,hQ⟩ := exists_preadjoint_of_trace_adjoint eN eM τN τM
    hLN hLM hτN hτM hfaithM E.includeMap E.expectMap (by
      intro a b
      have hh := congrArg star (hE b a)
      simp only [← map_star,star_mul,star_star] at hh
      rw [hEi]
      exact hh.symm)
  exact ⟨E,hEi,hE,⟨P,hPn.trans hEn,hP⟩,⟨Q,hQn.trans hIn,hQ⟩⟩

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M N X Y : Type*} [CStarAlgebra M] [CStarAlgebra N]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
variable (eM : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (eN : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N)

namespace ExpectedEmbedding
variable (E : ExpectedEmbedding N M)

lemma restrict_curryRight {n : ℕ} (f : Cochain M (n+1))
    (a : Fin n → N) (b : N) :
    (E.restrict f).curryRight a b =
      E.expectMap (f.curryRight (fun i => E.includeMap (a i)) (E.includeMap b)) := by
  simp only [ContinuousMultilinearMap.curryRight_apply,restrict_apply]
  congr 2
  funext i
  induction i using Fin.lastCases with
  | last => simp only [Fin.snoc_last]
  | cast i => simp only [Fin.snoc_castSucc]

 

lemma restrict_last_normal
    (P : Y →L[ℂ] X) (hP : ∀ a z, eN.symm (E.expectMap a) z=eM.symm a (P z))
    (Q : X →L[ℂ] Y) (hQ : ∀ a z, eM.symm (E.includeMap a) z=eN.symm a (Q z))
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ a : Fin n → M, HasPreadjoint eM (f.curryRight a)) :
    ∀ a : Fin n → N, HasPreadjoint eN ((E.restrict f).curryRight a) := by
  intro a z
  obtain ⟨w,hw⟩ := hf (fun i => E.includeMap (a i)) (P z)
  refine ⟨Q w,fun b => ?_⟩
  rw [E.restrict_curryRight,hP,hw,hQ]

end ExpectedEmbedding

section FiniteExactness
variable [PartialOrder M] [StarOrderedRing M] [PartialOrder N] [StarOrderedRing N]
  [CompleteSpace X] [CompleteSpace Y] [TopologicalSpace.SeparableSpace Y]
variable (τM : M →ₚ[ℂ] ℂ) (τN : N →ₚ[ℂ] ℂ)

 

theorem finite_exactness_of_separable_subalgebra
    (h1N : τN 1=1)
    (htrM : ∀ a b : M, τM (a*b)=τM (b*a)) (htrN : ∀ a b : N, τN (a*b)=τN (b*a))
    (hLM : ∀ b : M, HasPreadjoint eM (ContinuousLinearMap.mul ℂ M b))
    (hLN : ∀ b : N, HasPreadjoint eN (ContinuousLinearMap.mul ℂ N b))
    (hτM : TraceInPredual eM τM) (hτN : TraceInPredual eN τN)
    (hfaithM : ∀ a : M, τM (star a*a)=0 → a=0)
    (hfaithN : ∀ a : N, τN (star a*a)=0 → a=0)
    (I : N →⋆ₐ[ℂ] M) (hp : ∀ b : N, τM (I b)=τN b)
    (hpaths : HochschildRare.FinitePathTests τN)
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x, differentialValue f x=0)
    (hnormal : ∀ a : Fin n → M, HasPreadjoint eM (f.curryRight a))
    (S : Set M) (hS : ∀ a ∈ S, ∃ b, I b=a)
    (hfS : ∀ x : Fin (n+1) → M, (∀ i, x i ∈ S) → ∃ b, I b=f x) :
    ∃ G : Cochain M n, ‖G‖ ≤ ‖f‖ ∧
      ∀ x : Fin (n+1) → M, (∀ i, x i ∈ S) → differentialValue G x=f x := by
  obtain ⟨E,hEi,hE,⟨P,_,hP⟩,⟨Q,_,hQ⟩⟩ := exists_normal_expected_embedding
    eM eN τM τN htrM htrN hLM hLN hτM hτN hfaithM hfaithN I hp
  have hRN := right_hasPreadjoint_of_left eN τN hLN hτN hfaithN htrN
  obtain ⟨g,hgn,hg⟩ := primitive_of_separable_normal_finite_paths eN τN h1N htrN
    hfaithN hLN hRN hτN hpaths (E.restrict f) (E.restrict_cocycle f hf)
    (E.restrict_last_normal eM eN P hP Q hQ f hnormal)
  refine ⟨E.extend g,(E.extend_norm g).trans (hgn.trans (E.restrict_norm f)),?_⟩
  apply E.finite_exactness f g hg S
  · intro a ha
    obtain ⟨b,hb⟩ := hS a ha
    exact ⟨b,(hEi b).trans hb⟩
  · intro x hx
    obtain ⟨b,hb⟩ := hfS x hx
    exact ⟨b,(hEi b).trans hb⟩

end FiniteExactness

end BoundedHochschild
end

end OAI
