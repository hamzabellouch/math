import Mathlib
import OAI.Analysis.BoundedHochschild.NormalMultiplication

namespace OAI

/-! Normal vectors and projections for Hilbert-space representations. -/

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
namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

 

def predualEmbedding : X →ₗᵢ⋆[ℂ] StrongDual ℂ M where
  toFun z := (starL ℂ).toContinuousLinearMap.comp (((ContinuousLinearMap.apply ℂ ℂ) z).comp
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  map_add' z w := by ext a; simp
  map_smul' r z := by ext a; simp
  norm_map' z := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro a
      change ‖star (e.symm a z)‖ ≤ ‖z‖*‖a‖
      simpa only [norm_star,e.symm.norm_map,mul_comm] using (e.symm a).le_opNorm z
    · apply NormedSpace.norm_le_dual_bound ℂ z (norm_nonneg _)
      intro f
      have := ((starL ℂ).toContinuousLinearMap.comp (((ContinuousLinearMap.apply ℂ ℂ) z).comp
        e.symm.toContinuousLinearEquiv.toContinuousLinearMap)).le_opNorm (e f)
      change ‖f z‖ ≤ ‖(starL ℂ).toContinuousLinearMap.comp
        (((ContinuousLinearMap.apply ℂ ℂ) z).comp
        e.symm.toContinuousLinearEquiv.toContinuousLinearMap)‖ * ‖f‖
      simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
        ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        starL_apply,e.symm_apply_apply,norm_star,e.norm_map] using this

@[simp] lemma predualEmbedding_apply (z : X) (a : M) :
    predualEmbedding e z a=star (e.symm a z) := rfl

 
def normalDual : Submodule ℂ (StrongDual ℂ M) := (predualEmbedding e).toLinearMap.range

lemma mem_normalDual (φ : StrongDual ℂ M) :
    φ ∈ normalDual e ↔ ∃ z : X, ∀ a : M, φ a=star (e.symm a z) := by
  constructor
  · rintro ⟨z,rfl⟩; exact ⟨z,fun _ => rfl⟩
  · rintro ⟨z,hz⟩; exact ⟨z,ContinuousLinearMap.ext (fun a => (hz a).symm)⟩

variable [CompleteSpace X]

lemma normalDual_closed : IsClosed (normalDual e : Set (StrongDual ℂ M)) :=
  (predualEmbedding e).isometry.isClosedEmbedding.isClosed_range

omit [CompleteSpace X] in
lemma normalDual_comp {φ : StrongDual ℂ M} (hφ : φ ∈ normalDual e)
    (L : M →L[ℂ] M) (hL : BoundedHochschild.HasPreadjoint e L) :
    φ.comp L ∈ normalDual e := by
  obtain ⟨z,hz⟩ := (mem_normalDual e φ).mp hφ
  obtain ⟨w,hw⟩ := hL z
  exact (mem_normalDual e _).mpr ⟨w,fun a => by simp only [ContinuousLinearMap.comp_apply,hz,hw]⟩

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))

 
def coefficient (η : H) : H →L[ℂ] StrongDual ℂ M := by
  let L : H →ₗ[ℂ] StrongDual ℂ M :=
    { toFun := fun ξ => (innerSL ℂ η).comp
        (((ContinuousLinearMap.apply ℂ H) ξ).comp (π.toAlgHom.toLinearMap.mkContinuous 1 (fun a => by simpa using NonUnitalStarAlgHom.norm_apply_le π a)))
      map_add' := by intro ξ ζ; ext a; simp
      map_smul' := by intro r ξ; ext a; simp }
  exact L.mkContinuous ‖η‖ (by
    intro ξ
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro a
    change ‖⟪η,π a ξ⟫_ℂ‖ ≤ (‖η‖*‖ξ‖)*‖a‖
    calc
      _ ≤ ‖η‖*‖π a ξ‖ := norm_inner_le_norm _ _
      _ ≤ ‖η‖*(‖π a‖*‖ξ‖) := mul_le_mul_of_nonneg_left ((π a).le_opNorm ξ) (norm_nonneg _)
      _ ≤ ‖η‖*(‖a‖*‖ξ‖) := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π a
      _ = _ := by ring)

@[simp] lemma coefficient_apply (η ξ : H) (a : M) :
    coefficient π η ξ a=⟪η,π a ξ⟫_ℂ := rfl

lemma coefficient_norm (η ξ : H) : ‖coefficient π η ξ‖ ≤ ‖η‖*‖ξ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro a
  calc
    _ ≤ ‖η‖*‖π a ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖η‖*(‖π a‖*‖ξ‖) := by gcongr; exact (π a).le_opNorm ξ
    _ ≤ ‖η‖*(‖a‖*‖ξ‖) := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π a
    _ = _ := by ring

 
def normalVectors : Submodule ℂ H := ⨅ η : H, (normalDual e).comap (coefficient π η).toLinearMap

omit [CompleteSpace X] in
lemma mem_normalVectors (ξ : H) :
    ξ ∈ normalVectors e π ↔ ∀ η, coefficient π η ξ ∈ normalDual e := by
  simp only [normalVectors,Submodule.mem_iInf,Submodule.mem_comap,ContinuousLinearMap.coe_coe]

lemma normalVectors_closed : IsClosed (normalVectors e π : Set H) := by
  have hs : (normalVectors e π : Set H)=⋂ η : H, (coefficient π η) ⁻¹' (normalDual e : Set (StrongDual ℂ M)) := by
    ext ξ; simp only [Set.mem_iInter,Set.mem_preimage,SetLike.mem_coe,mem_normalVectors]
  rw [hs]
  exact isClosed_iInter fun η => (normalDual_closed e).preimage (coefficient π η).continuous

instance normalVectors_complete : CompleteSpace (normalVectors e π) :=
  (normalVectors_closed e π).completeSpace_coe

lemma normalVectors_mul {ξ : H} (hξ : ξ ∈ normalVectors e π) (b : M) :
    π b ξ ∈ normalVectors e π := by
  rw [mem_normalVectors] at hξ ⊢
  intro η
  have hc : coefficient π η (π b ξ) =
      (coefficient π η ξ).comp ((ContinuousLinearMap.mul ℂ M).flip b) := by
    ext a; simp [map_mul]
  rw [hc]
  exact normalDual_comp e (hξ η) _ ((HochschildSakai.abstract_multiplication_normal e).2 b)

omit [CompleteSpace X] in
lemma normalVectors_commutant {ξ : H} (hξ : ξ ∈ normalVectors e π)
    (T : H →L[ℂ] H) (hT : ∀ a : M, T * π a=π a*T) :
    T ξ ∈ normalVectors e π := by
  rw [mem_normalVectors] at hξ ⊢
  intro η
  have hc : coefficient π η (T ξ)=coefficient π (star T η) ξ := by
    ext a
    change ⟪η,π a (T ξ)⟫_ℂ=⟪T.adjoint η,π a ξ⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact congrArg (inner ℂ η) (congrArg (fun S : H →L[ℂ] H => S ξ) (hT a).symm)
  rw [hc]
  exact hξ _

 

lemma projection_commutes (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : H →L[ℂ] H)
    (hT : ∀ ξ ∈ K, T ξ ∈ K) (hTstar : ∀ ξ ∈ K, star T ξ ∈ K) :
    K.starProjection*T=T*K.starProjection := by
  ext ξ
  change K.starProjection (T ξ)=T (K.starProjection ξ)
  apply Submodule.eq_starProjection_of_mem_orthogonal (hT _ (by simp))
  intro η hη
  change ⟪η,T ξ-T (K.starProjection ξ)⟫_ℂ=0
  rw [← map_sub]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact K.sub_starProjection_mem_orthogonal ξ _ (hTstar η hη)

 
def normalProjection : H →L[ℂ] H := (normalVectors e π).starProjection

lemma normalProjection_mul (a : M) :
    normalProjection e π*π a=π a*normalProjection e π := by
  apply projection_commutes
  · intro ξ hξ; exact normalVectors_mul e π hξ a
  · intro ξ hξ
    rw [← map_star]
    exact normalVectors_mul e π hξ (star a)

lemma normalProjection_commutant (T : H →L[ℂ] H)
    (hT : ∀ a : M, T*π a=π a*T) :
    normalProjection e π*T=T*normalProjection e π := by
  apply projection_commutes
  · intro ξ hξ; exact normalVectors_commutant e π hξ T hT
  · intro ξ hξ
    apply normalVectors_commutant e π hξ
    intro a
    have h := congrArg star (hT (star a))
    simpa only [star_mul,← map_star,star_star] using h.symm

 
def coefficientLeft (ξ : H) : H →L⋆[ℂ] StrongDual ℂ M := by
  let L : H →ₗ⋆[ℂ] StrongDual ℂ M :=
    { toFun := fun η => coefficient π η ξ
      map_add' := by intro η ζ; ext a; simp
      map_smul' := by intro r η; ext a; simp [mul_comm] }
  exact L.mkContinuous ‖ξ‖ (fun η => by
    change ‖coefficient π η ξ‖ ≤ ‖ξ‖*‖η‖
    simpa only [mul_comm] using coefficient_norm π η ξ)

@[simp] lemma coefficientLeft_apply (ξ η : H) :
    coefficientLeft π ξ η=coefficient π η ξ := rfl

 
def cyclicSpace (ξ : H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range fun a : M => π a ξ)).topologicalClosure

lemma cyclicSpace_closed (ξ : H) : IsClosed (cyclicSpace π ξ : Set H) :=
  Submodule.isClosed_topologicalClosure _

instance cyclicSpace_complete (ξ : H) : CompleteSpace (cyclicSpace π ξ) :=
  (cyclicSpace_closed π ξ).completeSpace_coe

lemma cyclicSpace_mem (ξ : H) : ξ ∈ cyclicSpace π ξ := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨1,by simp⟩

lemma cyclicSpace_mul (ξ : H) (b : M) {ζ : H} (hζ : ζ ∈ cyclicSpace π ξ) :
    π b ζ ∈ cyclicSpace π ξ := by
  let S := cyclicSpace π ξ
  have hle : (Submodule.span ℂ (Set.range fun a : M => π a ξ)).topologicalClosure ≤
      S.comap (π b).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨a,rfl⟩
      change π b (π a ξ) ∈ S
      change π b (π a ξ) ∈ (Submodule.span ℂ (Set.range fun a : M => π a ξ)).topologicalClosure
      apply Submodule.le_topologicalClosure
      rw [← mul_apply_eq_comp,← map_mul]
      exact Submodule.subset_span (Set.mem_range_self (b*a))
    · exact (cyclicSpace_closed π ξ).preimage (π b).continuous
  exact hle hζ

lemma cyclicProjection_mul (ξ : H) (a : M) :
    (cyclicSpace π ξ).starProjection*π a=π a*(cyclicSpace π ξ).starProjection := by
  apply projection_commutes
  · intro ζ hζ; exact cyclicSpace_mul π ξ a hζ
  · intro ζ hζ
    rw [← map_star]
    exact cyclicSpace_mul π ξ (star a) hζ

 

lemma cyclic_coefficients_normal (η ξ : H)
    (h : coefficient π η ξ ∈ normalDual e) {ζ : H} (hζ : ζ ∈ cyclicSpace π η) :
    coefficient π ζ ξ ∈ normalDual e := by
  let S := (normalDual e).comap (coefficientLeft π ξ).toLinearMap
  have hle : cyclicSpace π η ≤ S := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨b,rfl⟩
      change coefficient π (π b η) ξ ∈ normalDual e
      have hc : coefficient π (π b η) ξ=(coefficient π η ξ).comp
          (ContinuousLinearMap.mul ℂ M (star b)) := by
        ext a
        change ⟪π b η,π a ξ⟫_ℂ=⟪η,π (star b*a) ξ⟫_ℂ
        rw [map_mul,mul_apply_eq_comp,map_star]
        exact (ContinuousLinearMap.adjoint_inner_right (π b) η (π a ξ)).symm
      rw [hc]
      exact normalDual_comp e h _ ((HochschildSakai.abstract_multiplication_normal e).1 _)
    · exact (normalDual_closed e).preimage (coefficientLeft π ξ).continuous
  exact hle hζ

 

lemma normalProjection_fixes_normal (η ξ : H)
    (h : coefficient π η ξ ∈ normalDual e) :
    coefficient π η (normalProjection e π ξ)=coefficient π η ξ := by
  let K := cyclicSpace π η
  let Q := K.starProjection
  have hQ : ∀ a : M, Q*π a=π a*Q := cyclicProjection_mul π η
  have hcoef (ζ : H) : coefficient π ζ (Q ξ)=coefficient π (Q ζ) ξ := by
    ext a
    change ⟪ζ,π a (Q ξ)⟫_ℂ=⟪Q ζ,π a ξ⟫_ℂ
    have hc := congrArg (fun T : H →L[ℂ] H => T ξ) (hQ a)
    change Q (π a ξ)=π a (Q ξ) at hc
    rw [← hc]
    exact (K.inner_starProjection_left_eq_right ζ (π a ξ)).symm
  have hn : Q ξ ∈ normalVectors e π := by
    rw [mem_normalVectors]
    intro ζ
    rw [hcoef]
    exact cyclic_coefficients_normal e π η ξ h (by simp [Q,K])
  have hP : normalProjection e π (Q ξ)=Q ξ :=
    Submodule.starProjection_eq_self_iff.mpr hn
  have hcomm := congrArg (fun T : H →L[ℂ] H => T ξ) (normalProjection_commutant e π Q hQ)
  change normalProjection e π (Q ξ)=Q (normalProjection e π ξ) at hcomm
  have hη : Q η=η := Submodule.starProjection_eq_self_iff.mpr (cyclicSpace_mem π η)
  calc
    coefficient π η (normalProjection e π ξ) = coefficient π (Q η) (normalProjection e π ξ) := by rw [hη]
    _ = coefficient π η (Q (normalProjection e π ξ)) := by
      ext a
      change ⟪Q η,π a (normalProjection e π ξ)⟫_ℂ=⟪η,π a (Q (normalProjection e π ξ))⟫_ℂ
      rw [K.inner_starProjection_left_eq_right]
      exact congrArg (inner ℂ η) (congrArg (fun T : H →L[ℂ] H => T (normalProjection e π ξ)) (hQ a))
    _ = coefficient π η (Q ξ) := by rw [← hcomm,hP]
    _ = coefficient π (Q η) ξ := hcoef η
    _ = coefficient π η ξ := by rw [hη]

end HochschildNormalPart

 

open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v w
variable {M : Type u} [CStarAlgebra M]
variable {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

 
def sumOperator (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    WithLp 2 (H × K) →L[ℂ] WithLp 2 (H × K) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap.comp
    ((T.prodMap S).comp (WithLp.prodContinuousLinearEquiv 2 ℂ H K).toContinuousLinearMap)

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] lemma sumOperator_apply (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : WithLp 2 (H×K)) :
    sumOperator T S x=WithLp.toLp 2 (T x.fst,S x.snd) := rfl

 
def sumRepresentation (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    M →⋆ₐ[ℂ] (WithLp 2 (H×K) →L[ℂ] WithLp 2 (H×K)) where
  toFun a := sumOperator (π a) (ρ a)
  map_zero' := by ext x; simp
  map_one' := by ext x; simp; rfl
  map_add' a b := by ext x; simp; rfl
  map_mul' a b := by ext x; simp [map_mul,mul_apply_eq_comp]
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one]; rfl
  map_star' a := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [sumOperator_apply,WithLp.prod_inner_apply,
      map_star,ContinuousLinearMap.star_eq_adjoint]
    simp only [ContinuousLinearMap.adjoint_inner_left]
    rfl

@[simp] lemma sumRepresentation_apply (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (a : M) (x : WithLp 2 (H×K)) :
    sumRepresentation π ρ a x=WithLp.toLp 2 (π a x.fst,ρ a x.snd) := rfl

lemma coefficient_sum (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (η ξ : WithLp 2 (H×K)) :
    coefficient (sumRepresentation π ρ) η ξ=
      coefficient π η.fst ξ.fst+coefficient ρ η.snd ξ.snd := by
  ext a; rfl

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K))

omit [CompleteSpace X] in
lemma mem_normalVectors_sum (ξ : WithLp 2 (H×K)) :
    ξ ∈ normalVectors e (sumRepresentation π ρ) ↔
      ξ.fst ∈ normalVectors e π ∧ ξ.snd ∈ normalVectors e ρ := by
  simp only [mem_normalVectors,coefficient_sum]
  constructor
  · intro h
    constructor
    · intro η
      have h' := h (WithLp.toLp 2 (η,0))
      change coefficient π η ξ.fst+coefficient ρ 0 ξ.snd ∈ normalDual e at h'
      have hz : coefficient ρ 0 ξ.snd=0 := by ext a; simp
      simpa only [hz,add_zero] using h'
    · intro η
      have h' := h (WithLp.toLp 2 (0,η))
      change coefficient π 0 ξ.fst+coefficient ρ η ξ.snd ∈ normalDual e at h'
      have hz : coefficient π 0 ξ.fst=0 := by ext a; simp
      simpa only [hz,zero_add] using h'
  · rintro ⟨hπ,hρ⟩ η
    exact (normalDual e).add_mem (hπ η.fst) (hρ η.snd)

 
lemma normalProjection_sum (ξ : WithLp 2 (H×K)) :
    normalProjection e (sumRepresentation π ρ) ξ=
      WithLp.toLp 2 (normalProjection e π ξ.fst,normalProjection e ρ ξ.snd) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · rw [mem_normalVectors_sum]
    change normalProjection e π ξ.fst ∈ normalVectors e π ∧
      normalProjection e ρ ξ.snd ∈ normalVectors e ρ
    exact ⟨by simp [normalProjection],by simp [normalProjection]⟩
  · intro η hη
    obtain ⟨hη₁,hη₂⟩ := (mem_normalVectors_sum e π ρ η).mp hη
    change ⟪η,ξ-WithLp.toLp 2 (normalProjection e π ξ.fst,normalProjection e ρ ξ.snd)⟫_ℂ=0
    change ⟪η.fst,ξ.fst-normalProjection e π ξ.fst⟫_ℂ+
      ⟪η.snd,ξ.snd-normalProjection e ρ ξ.snd⟫_ℂ=0
    unfold normalProjection
    rw [(normalVectors e π).sub_starProjection_mem_orthogonal ξ.fst η.fst hη₁,
      (normalVectors e ρ).sub_starProjection_mem_orthogonal ξ.snd η.snd hη₂,add_zero]

 

lemma coefficient_normal_eq_of_eq
    (η ξ : H) (ζ ω : K) (h : coefficient π η ξ=coefficient ρ ζ ω) :
    coefficient π η (normalProjection e π ξ)=coefficient ρ ζ (normalProjection e ρ ω) := by
  let A : WithLp 2 (H×K) := WithLp.toLp 2 (η,ζ)
  let B : WithLp 2 (H×K) := WithLp.toLp 2 (ξ,-ω)
  have hz : coefficient (sumRepresentation π ρ) A B=0 := by
    rw [coefficient_sum]
    change coefficient π η ξ+coefficient ρ ζ (-ω)=0
    rw [map_neg,h,add_neg_cancel]
  have hn : coefficient (sumRepresentation π ρ) A B ∈ normalDual e := hz ▸ (normalDual e).zero_mem
  have hp := normalProjection_fixes_normal e (sumRepresentation π ρ) A B hn
  rw [hz,normalProjection_sum,coefficient_sum] at hp
  change coefficient π η (normalProjection e π ξ)+coefficient ρ ζ (normalProjection e ρ (-ω))=0 at hp
  rw [map_neg,map_neg] at hp
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hp)

end HochschildNormalPart
end

end OAI
