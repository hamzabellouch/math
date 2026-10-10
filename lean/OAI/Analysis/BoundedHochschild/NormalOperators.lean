import Mathlib
import OAI.Analysis.BoundedHochschild.NormalVectors
import OAI.Analysis.BoundedHochschild.PositiveDecomposition

namespace OAI

/-! Normal parts of scalar functionals and bounded operators. -/

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
namespace HochschildNormalPart
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

 
def positiveVector (ψ : M →ₚ[ℂ] ℂ) : ψ.GNS := (ψ.toPreGNS 1 : ψ.PreGNS)

lemma positiveVector_coefficient (ψ : M →ₚ[ℂ] ℂ) (a : M) :
    coefficient ψ.gnsStarAlgHom (positiveVector ψ) (positiveVector ψ) a=ψ a := by
  change ⟪(ψ.toPreGNS 1 : ψ.GNS),ψ.gnsNonUnitalStarAlgHom a (ψ.toPreGNS 1)⟫_ℂ=ψ a
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,UniformSpace.Completion.inner_coe]
  simp [PositiveLinearMap.preGNS_inner_def]

lemma positiveVector_norm_sq (ψ : M →ₚ[ℂ] ℂ) : ‖positiveVector ψ‖^2=‖ψ 1‖ := by
  have hv := positiveVector_coefficient ψ (1:M)
  simp only [coefficient_apply,map_one] at hv
  change ⟪positiveVector ψ,positiveVector ψ⟫_ℂ=ψ 1 at hv
  rw [inner_self_eq_norm_sq_to_K] at hv
  rw [← hv,norm_pow]
  simp

abbrev FourHilbert (ψ : Fin 4 → M →ₚ[ℂ] ℂ) :=
  WithLp 2 ((WithLp 2 ((ψ 0).GNS × (ψ 1).GNS)) ×
    (WithLp 2 ((ψ 2).GNS × (ψ 3).GNS)))

def fourRepresentation (ψ : Fin 4 → M →ₚ[ℂ] ℂ) :
    M →⋆ₐ[ℂ] (FourHilbert ψ →L[ℂ] FourHilbert ψ) :=
  sumRepresentation (sumRepresentation (ψ 0).gnsStarAlgHom (ψ 1).gnsStarAlgHom)
    (sumRepresentation (ψ 2).gnsStarAlgHom (ψ 3).gnsStarAlgHom)

def fourLeft (ψ : Fin 4 → M →ₚ[ℂ] ℂ) : FourHilbert ψ :=
  WithLp.toLp 2 (WithLp.toLp 2 (positiveVector (ψ 0),-positiveVector (ψ 1)),
    WithLp.toLp 2 (-Complex.I • positiveVector (ψ 2),Complex.I • positiveVector (ψ 3)))

def fourRight (ψ : Fin 4 → M →ₚ[ℂ] ℂ) : FourHilbert ψ :=
  WithLp.toLp 2 (WithLp.toLp 2 (positiveVector (ψ 0),positiveVector (ψ 1)),
    WithLp.toLp 2 (positiveVector (ψ 2),positiveVector (ψ 3)))

lemma four_coefficient (ψ : Fin 4 → M →ₚ[ℂ] ℂ) (a : M) :
    coefficient (fourRepresentation ψ) (fourLeft ψ) (fourRight ψ) a=
      ψ 0 a-ψ 1 a+Complex.I*(ψ 2 a-ψ 3 a) := by
  rw [fourRepresentation,coefficient_sum,add_apply]
  simp only [fourLeft,fourRight,WithLp.toLp_fst,WithLp.toLp_snd,coefficient_sum,
    add_apply,coefficient_apply,inner_neg_left,inner_smul_left]
  simp only [← coefficient_apply,positiveVector_coefficient,map_neg,Complex.conj_I]
  ring

lemma four_norm_bound (φ : StrongDual ℂ M) (ψ : Fin 4 → M →ₚ[ℂ] ℂ)
    (hψ : ∀ i,‖ψ i 1‖≤‖φ‖) : ‖fourLeft ψ‖*‖fourRight ψ‖≤4*‖φ‖ := by
  have hr : ‖fourRight ψ‖^2=‖ψ 0 1‖+‖ψ 1 1‖+(‖ψ 2 1‖+‖ψ 3 1‖) := by
    simp only [fourRight,WithLp.prod_norm_sq_eq_of_L2,WithLp.toLp_fst,WithLp.toLp_snd,
      positiveVector_norm_sq]
  have hl : ‖fourLeft ψ‖^2=‖fourRight ψ‖^2 := by
    rw [hr]
    simp only [fourLeft,WithLp.prod_norm_sq_eq_of_L2,WithLp.toLp_fst,WithLp.toLp_snd,
      norm_neg,norm_smul,Complex.norm_I,one_mul,positiveVector_norm_sq]
  have he : ‖fourLeft ψ‖=‖fourRight ψ‖ := by nlinarith [norm_nonneg (fourLeft ψ),norm_nonneg (fourRight ψ)]
  rw [he,← sq,hr]
  linarith [hψ 0,hψ 1,hψ 2,hψ 3]

 
structure FunctionalModel (φ : StrongDual ℂ M) where
  H : Type u
  [normed : NormedAddCommGroup H]
  [innerSpace : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
  representation : M →⋆ₐ[ℂ] (H →L[ℂ] H)
  leftVector : H
  rightVector : H
  realizes : coefficient representation leftVector rightVector=φ
  bound : ‖leftVector‖*‖rightVector‖≤4*‖φ‖
attribute [instance] FunctionalModel.normed FunctionalModel.innerSpace FunctionalModel.complete

lemma functionalModel_nonempty (φ : StrongDual ℂ M) : Nonempty (FunctionalModel φ) := by
  obtain ⟨ψ,hψ,hφ⟩ := HochschildPositiveDecomposition.exists_four_positive φ
  refine ⟨{ H := FourHilbert ψ
            representation := fourRepresentation ψ
            leftVector := fourLeft ψ
            rightVector := fourRight ψ
            realizes := ?_
            bound := four_norm_bound φ ψ hψ }⟩
  ext a
  exact (four_coefficient ψ a).trans (hφ a).symm

end HochschildNormalPart

 

namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def functionalModel (φ : StrongDual ℂ M) : FunctionalModel φ := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  exact Classical.choice (functionalModel_nonempty φ)

 
def normalPartRaw (φ : StrongDual ℂ M) : StrongDual ℂ M :=
  coefficient (functionalModel φ).representation (functionalModel φ).leftVector
    (normalProjection e (functionalModel φ).representation (functionalModel φ).rightVector)

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma normalPartRaw_coefficient (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    normalPartRaw e (coefficient π η ξ)=coefficient π η (normalProjection e π ξ) := by
  exact coefficient_normal_eq_of_eq e _ π _ _ η ξ (functionalModel _).realizes

lemma normalPartRaw_add (φ ψ : StrongDual ℂ M) :
    normalPartRaw e (φ+ψ)=normalPartRaw e φ+normalPartRaw e ψ := by
  let m := functionalModel φ
  let n := functionalModel ψ
  let π := sumRepresentation m.representation n.representation
  let η : WithLp 2 (m.H×n.H) := WithLp.toLp 2 (m.leftVector,n.leftVector)
  let ξ : WithLp 2 (m.H×n.H) := WithLp.toLp 2 (m.rightVector,n.rightVector)
  have hc : coefficient π η ξ=φ+ψ := by
    rw [coefficient_sum]
    change coefficient m.representation m.leftVector m.rightVector+
      coefficient n.representation n.leftVector n.rightVector=φ+ψ
    rw [m.realizes,n.realizes]
  rw [← hc,normalPartRaw_coefficient,normalProjection_sum,coefficient_sum]
  rfl

lemma normalPartRaw_smul (r : ℂ) (φ : StrongDual ℂ M) :
    normalPartRaw e (r • φ)=r • normalPartRaw e φ := by
  let m := functionalModel φ
  have hc : coefficient m.representation m.leftVector (r • m.rightVector)=r • φ := by
    rw [map_smul,m.realizes]
  rw [← hc,normalPartRaw_coefficient,map_smul,map_smul]
  rfl

lemma normalPartRaw_norm (φ : StrongDual ℂ M) : ‖normalPartRaw e φ‖≤4*‖φ‖ := by
  let m := functionalModel φ
  exact (coefficient_norm _ _ _).trans
    ((mul_le_mul_of_nonneg_left ((normalVectors e m.representation).norm_starProjection_apply_le _)
      (norm_nonneg m.leftVector)).trans m.bound)

 

def scalarNormalPart : StrongDual ℂ M →L[ℂ] StrongDual ℂ M :=
  LinearMap.mkContinuous
    { toFun := normalPartRaw e
      map_add' := normalPartRaw_add e
      map_smul' := normalPartRaw_smul e } 4 (normalPartRaw_norm e)

@[simp] lemma scalarNormalPart_coefficient (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    scalarNormalPart e (coefficient π η ξ)=coefficient π η (normalProjection e π ξ) :=
  normalPartRaw_coefficient e π η ξ

lemma scalarNormalPart_norm : ‖scalarNormalPart e‖≤4 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) (normalPartRaw_norm e)

lemma scalarNormalPart_mem (φ : StrongDual ℂ M) : scalarNormalPart e φ ∈ normalDual e := by
  apply (mem_normalVectors e (functionalModel φ).representation _).mp
  simp [normalProjection]

lemma scalarNormalPart_fixes {φ : StrongDual ℂ M} (hφ : φ ∈ normalDual e) :
    scalarNormalPart e φ=φ := by
  let m := functionalModel φ
  change coefficient m.representation m.leftVector (normalProjection e m.representation m.rightVector)=φ
  rw [normalProjection_fixes_normal e _ _ _ (m.realizes.symm ▸ hφ),m.realizes]

lemma scalarNormalPart_comp_left (φ : StrongDual ℂ M) (b : M) :
    scalarNormalPart e (φ.comp (ContinuousLinearMap.mul ℂ M b))=
      (scalarNormalPart e φ).comp (ContinuousLinearMap.mul ℂ M b) := by
  let m := functionalModel φ
  have hc (ξ : m.H) : (coefficient m.representation m.leftVector ξ).comp
      (ContinuousLinearMap.mul ℂ M b)=coefficient m.representation (m.representation (star b) m.leftVector) ξ := by
    ext a
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply',coefficient_apply,
      map_mul,mul_apply_eq_comp,map_star,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  rw [← m.realizes,hc,scalarNormalPart_coefficient,scalarNormalPart_coefficient,hc]

lemma scalarNormalPart_comp_right (φ : StrongDual ℂ M) (b : M) :
    scalarNormalPart e (φ.comp ((ContinuousLinearMap.mul ℂ M).flip b))=
      (scalarNormalPart e φ).comp ((ContinuousLinearMap.mul ℂ M).flip b) := by
  let m := functionalModel φ
  have hc (ξ : m.H) : (coefficient m.representation m.leftVector ξ).comp
      ((ContinuousLinearMap.mul ℂ M).flip b)=coefficient m.representation m.leftVector (m.representation b ξ) := by
    ext a
    simp [map_mul]
  rw [← m.realizes,hc,scalarNormalPart_coefficient,scalarNormalPart_coefficient,hc]
  exact congrArg (coefficient m.representation m.leftVector)
    (congrArg (fun T : m.H →L[ℂ] m.H => T m.rightVector) (normalProjection_mul e m.representation b))

end HochschildNormalPart

 

namespace HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

omit [CompleteSpace X] in
lemma predual_separates {a b : M}
    (h : ∀ z,predualEmbedding e z a=predualEmbedding e z b) : a=b := by
  apply e.symm.injective
  ext z
  exact star_injective (h z)

def normalPredualVector (T : M →L[ℂ] M) (z : X) : X :=
  Classical.choose ((mem_normalDual e _).mp (scalarNormalPart_mem e ((predualEmbedding e z).comp T)))

lemma normalPredualVector_spec (T : M →L[ℂ] M) (z : X) :
    predualEmbedding e (normalPredualVector e T z)=
      scalarNormalPart e ((predualEmbedding e z).comp T) := by
  ext a
  exact (Classical.choose_spec ((mem_normalDual e _).mp
    (scalarNormalPart_mem e ((predualEmbedding e z).comp T))) a).symm

lemma normalPredualVector_add (T : M →L[ℂ] M) (z w : X) :
    normalPredualVector e T (z+w)=normalPredualVector e T z+normalPredualVector e T w := by
  apply (predualEmbedding e).injective
  simp only [normalPredualVector_spec,map_add,ContinuousLinearMap.add_comp]

lemma normalPredualVector_smul (T : M →L[ℂ] M) (c : ℂ) (z : X) :
    normalPredualVector e T (c • z)=c • normalPredualVector e T z := by
  apply (predualEmbedding e).injective
  simp only [normalPredualVector_spec,map_smulₛₗ,ContinuousLinearMap.smul_comp,RingHom.id_apply]

lemma normalPredualVector_norm (T : M →L[ℂ] M) (z : X) :
    ‖normalPredualVector e T z‖≤(4*‖T‖)*‖z‖ := by
  rw [← (predualEmbedding e).norm_map,normalPredualVector_spec]
  calc
    _ ≤ 4*‖(predualEmbedding e z).comp T‖ := (scalarNormalPart e).le_of_opNorm_le (scalarNormalPart_norm e) _
    _ ≤ 4*(‖predualEmbedding e z‖*‖T‖) := by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = (4*‖T‖)*‖z‖ := by rw [(predualEmbedding e).norm_map]; ring

def normalPreadjoint (T : M →L[ℂ] M) : X →L[ℂ] X :=
  LinearMap.mkContinuous
    { toFun := normalPredualVector e T
      map_add' := normalPredualVector_add e T
      map_smul' := normalPredualVector_smul e T } (4*‖T‖) (normalPredualVector_norm e T)

def normalOperator (T : M →L[ℂ] M) : M →L[ℂ] M :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((ContinuousLinearMap.compL ℂ X X ℂ).flip (normalPreadjoint e T)).comp
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap)

lemma normalOperator_pairing (T : M →L[ℂ] M) (a : M) (z : X) :
    predualEmbedding e z (normalOperator e T a)=
      scalarNormalPart e ((predualEmbedding e z).comp T) a := by
  rw [← normalPredualVector_spec]
  simp [normalOperator,normalPreadjoint,predualEmbedding_apply]

lemma normalOperator_normal (T : M →L[ℂ] M) : BoundedHochschild.HasPreadjoint e (normalOperator e T) := by
  intro z
  refine ⟨normalPreadjoint e T z,?_⟩
  intro a
  simp [normalOperator]

lemma normalOperator_add (S T : M →L[ℂ] M) : normalOperator e (S+T)=normalOperator e S+normalOperator e T := by
  ext a
  apply predual_separates e
  intro z
  simp only [normalOperator_pairing,ContinuousLinearMap.comp_add,map_add,add_apply]

lemma normalOperator_smul (c : ℂ) (T : M →L[ℂ] M) : normalOperator e (c • T)=c • normalOperator e T := by
  ext a
  apply predual_separates e
  intro z
  simp only [normalOperator_pairing,ContinuousLinearMap.comp_smul,map_smul,smul_apply]

lemma normalOperator_norm (T : M →L[ℂ] M) : ‖normalOperator e T‖≤4*‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  rw [← e.symm.norm_map]
  change ‖e.symm (e ((e.symm a).comp (normalPreadjoint e T)))‖≤_
  rw [e.symm_apply_apply]
  calc
    _ ≤ ‖normalPreadjoint e T‖*‖e.symm a‖ := by
      simpa only [mul_comm] using (ContinuousLinearMap.opNorm_comp_le (e.symm a) (normalPreadjoint e T))
    _ ≤ (4*‖T‖)*‖a‖ := by
      rw [e.symm.norm_map]
      gcongr
      exact LinearMap.mkContinuous_norm_le _ (by positivity) (normalPredualVector_norm e T)

 
def operatorNormalPart : (M →L[ℂ] M) →L[ℂ] (M →L[ℂ] M) :=
  LinearMap.mkContinuous
    { toFun := normalOperator e
      map_add' := normalOperator_add e
      map_smul' := normalOperator_smul e } 4 (normalOperator_norm e)

lemma operatorNormalPart_pairing (T : M →L[ℂ] M) (a : M) (z : X) :
    predualEmbedding e z (operatorNormalPart e T a)=
      scalarNormalPart e ((predualEmbedding e z).comp T) a := normalOperator_pairing e T a z

lemma operatorNormalPart_normal (T : M →L[ℂ] M) :
    BoundedHochschild.HasPreadjoint e (operatorNormalPart e T) := normalOperator_normal e T

lemma operatorNormalPart_fixes (T : M →L[ℂ] M) (hT : BoundedHochschild.HasPreadjoint e T) :
    operatorNormalPart e T=T := by
  ext a
  apply predual_separates e
  intro z
  rw [operatorNormalPart_pairing]
  have hn : (predualEmbedding e z).comp T ∈ normalDual e :=
    normalDual_comp e (φ := predualEmbedding e z) ⟨z,rfl⟩ T hT
  exact congrArg (fun φ : StrongDual ℂ M => φ a) (scalarNormalPart_fixes e hn)

lemma operatorNormalPart_comp_normal (T L : M →L[ℂ] M)
    (hL : BoundedHochschild.HasPreadjoint e L) :
    operatorNormalPart e (L.comp T)=L.comp (operatorNormalPart e T) := by
  ext a
  apply predual_separates e
  intro z
  obtain ⟨w,hw⟩ := hL z
  have he : (predualEmbedding e z).comp L=predualEmbedding e w := by
    ext b
    simp only [ContinuousLinearMap.comp_apply,predualEmbedding_apply,hw]
  rw [operatorNormalPart_pairing,← ContinuousLinearMap.comp_assoc,he]
  change _=predualEmbedding e z (L (operatorNormalPart e T a))
  rw [← ContinuousLinearMap.comp_apply (predualEmbedding e z) L,he,operatorNormalPart_pairing]

lemma operatorNormalPart_comp_left (T : M →L[ℂ] M) (b : M) :
    operatorNormalPart e (T.comp (ContinuousLinearMap.mul ℂ M b))=
      (operatorNormalPart e T).comp (ContinuousLinearMap.mul ℂ M b) := by
  ext a
  apply predual_separates e
  intro z
  rw [operatorNormalPart_pairing,← ContinuousLinearMap.comp_assoc,scalarNormalPart_comp_left]
  exact (operatorNormalPart_pairing e T (b*a) z).symm

lemma operatorNormalPart_comp_right (T : M →L[ℂ] M) (b : M) :
    operatorNormalPart e (T.comp ((ContinuousLinearMap.mul ℂ M).flip b))=
      (operatorNormalPart e T).comp ((ContinuousLinearMap.mul ℂ M).flip b) := by
  ext a
  apply predual_separates e
  intro z
  rw [operatorNormalPart_pairing,← ContinuousLinearMap.comp_assoc,scalarNormalPart_comp_right]
  exact (operatorNormalPart_pairing e T (a*b) z).symm

end HochschildNormalPart
end

end OAI
