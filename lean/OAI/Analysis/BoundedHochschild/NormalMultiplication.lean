import Mathlib
import OAI.Analysis.BoundedHochschild.SpectralProjections

namespace OAI

/-! Preadjoints for left and right multiplication. -/

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
open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

 
def leftMatrixFunctional (z : X) (b : M) : StrongDual ℂ (StrongDual ℂ X) :=
  let L : StrongDual ℂ X →ₗ[ℂ] ℂ :=
    { toFun := fun f => e.symm (star b*e f) z
      map_add' := by intro f g; simp [mul_add]
      map_smul' := by intro r f; simp [map_smulₛₗ] }
  L.mkContinuous (‖b‖*‖z‖) (by
    intro f
    change ‖e.symm (star b*e f) z‖ ≤ _
    calc
      _ ≤ ‖e.symm (star b*e f)‖*‖z‖ := (e.symm (star b*e f)).le_opNorm z
      _ = ‖star b*e f‖*‖z‖ := by rw [e.symm.norm_map]
      _ ≤ (‖star b‖*‖e f‖)*‖z‖ := by gcongr; exact norm_mul_le _ _
      _ = (‖b‖*‖z‖)*‖f‖ := by rw [norm_star,e.norm_map]; ring)

lemma leftMatrixFunctional_apply (z : X) (b : M) (f : StrongDual ℂ X) :
    leftMatrixFunctional e z b f=e.symm (star b*e f) z := rfl

lemma leftMatrixFunctional_norm (z : X) (b : M) :
    ‖leftMatrixFunctional e z b‖ ≤ ‖z‖*‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg z) (norm_nonneg b))
  intro f
  rw [leftMatrixFunctional_apply]
  calc
    _ ≤ ‖e.symm (star b*e f)‖*‖z‖ := (e.symm (star b*e f)).le_opNorm z
    _ = ‖star b*e f‖*‖z‖ := by rw [e.symm.norm_map]
    _ ≤ (‖star b‖*‖e f‖)*‖z‖ := by gcongr; exact norm_mul_le _ _
    _ = (‖z‖*‖b‖)*‖f‖ := by rw [norm_star,e.norm_map]; ring

def starLeftMatrixMap (z : X) : M →L[ℂ] StrongDual ℂ (StrongDual ℂ X) := by
  let : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
  let : NormedAddCommGroup (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
  let K : M →ₗ[ℂ] StrongDual ℂ (StrongDual ℂ X) :=
    { toFun := leftMatrixFunctional e z
      map_add' := by
        intro b c
        ext f
        simp only [leftMatrixFunctional_apply,star_add,add_mul,map_add,
          add_apply]
      map_smul' := by
        intro r b
        ext f
        simp only [leftMatrixFunctional_apply,star_smul,smul_mul_assoc,map_smulₛₗ,
          smul_apply,RingHom.id_apply,starRingEnd_apply,
          star_star] }
  exact K.mkContinuous ‖z‖ (leftMatrixFunctional_norm e z)

lemma starLeftMatrixMap_apply (z : X) (b : M) (f : StrongDual ℂ X) :
    starLeftMatrixMap e z b f=e.symm (star b*e f) z := rfl

variable [PartialOrder M] [StarOrderedRing M] [CompleteSpace X]

 

theorem mul_hasPreadjoint (a : M) : HasPreadjoint e (ContinuousLinearMap.mul ℂ M a) := by
  intro z
  let : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
  let : NormedAddCommGroup (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
  let K := starLeftMatrixMap e z
  let J := NormedSpace.inclusionInDoubleDual ℂ X
  let S := (LinearMap.range J.toLinearMap).comap K.toLinearMap
  have hc : IsClosed (S : Set M) := by
    change IsClosed (K ⁻¹' Set.range J)
    apply IsClosed.preimage (f := K) K.continuous
    exact (NormedSpace.inclusionInDoubleDualLi ℂ (E := X)).isometry.isClosedEmbedding.isClosed_range
  have hspan : Submodule.span ℂ {p : M | IsStarProjection p} ≤ S := by
    apply Submodule.span_le.mpr
    intro p hp
    obtain ⟨w,hw⟩ := projection_mul_hasPreadjoint e p hp z
    refine ⟨w,?_⟩
    ext f
    change f w=e.symm (star p*e f) z
    rw [hp.isSelfAdjoint.star_eq]
    simpa using (hw (e f)).symm
  have htop : (⊤ : Submodule ℂ M) ≤ S := by
    rw [← projection_span_dense e]
    exact Submodule.topologicalClosure_minimal _ hspan hc
  obtain ⟨w,hw⟩ := htop (show star a ∈ (⊤ : Submodule ℂ M) from Submodule.mem_top)
  refine ⟨w,fun b => ?_⟩
  have hh := congrArg (fun G : StrongDual ℂ (StrongDual ℂ X) => G (e.symm b)) hw
  change e.symm b w=e.symm (star (star a)*e (e.symm b)) z at hh
  simpa using hh.symm

 
theorem predual_tendsto_mul_left (a : M) {b : I → M} {l : Filter I} {c : M}
    (hb : PredualTendsto e b l c) :
    PredualTendsto e (fun i => a*b i) l (a*c) :=
  HasPreadjoint.tendsto e (mul_hasPreadjoint e a) hb

 
theorem mul_right_hasPreadjoint (a : M) :
    HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a) := by
  intro z
  obtain ⟨w,hw⟩ := exists_star_predual_vector e z
  obtain ⟨v,hv⟩ := mul_hasPreadjoint e (star a) w
  obtain ⟨u,hu⟩ := exists_star_predual_vector e v
  refine ⟨u,fun b => ?_⟩
  have hh := hw (star a*star b)
  simp only [star_mul,star_star] at hh
  have hvb : e.symm (star a*star b) w=e.symm (star b) v := by
    simpa using hv (star b)
  rw [hvb,hu b,star_star] at hh
  simpa using hh

 
theorem predual_tendsto_mul_right (a : M) {b : I → M} {l : Filter I} {c : M}
    (hb : PredualTendsto e b l c) :
    PredualTendsto e (fun i => b i*a) l (c*a) :=
  HasPreadjoint.tendsto e (mul_right_hasPreadjoint e a) hb

end HochschildSakai

 

open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

 
theorem exists_abstract_star_preadjoint :
    ∃ P : X →L⋆[ℂ] X, ‖P‖ ≤ 1 ∧
      ∀ a z, e.symm (star a) z=star (e.symm a (P z)) := by
  classical
  choose P hP using exists_star_predual_vector e
  have heq {x y : X} (h : ∀ a : M, e.symm a x=e.symm a y) : x=y := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    intro f
    simpa only [e.symm_apply_apply] using h (e f)
  have hPa (x y : X) : P (x+y)=P x+P y := by
    apply heq
    intro a
    apply star_injective
    rw [← hP (x+y) a,map_add,map_add,star_add,← hP x a,← hP y a]
  have hPs (r : ℂ) (x : X) : P (r • x)=star r • P x := by
    apply heq
    intro a
    apply star_injective
    rw [← hP (r • x) a,map_smul,map_smul,star_smul,star_star,← hP x a]
  let L : X →ₗ⋆[ℂ] X :=
    { toFun := P
      map_add' := hPa
      map_smul' := hPs }
  have hb (z : X) : ‖L z‖ ≤ 1*‖z‖ := by
    rw [one_mul]
    apply NormedSpace.norm_le_dual_bound ℂ _ (norm_nonneg _)
    intro f
    have hn := congrArg norm (hP z (e f))
    simp only [norm_star,e.symm_apply_apply] at hn
    change ‖f (P z)‖ ≤ ‖z‖*‖f‖
    rw [mul_comm ‖z‖]
    rw [← hn]
    simpa only [e.symm.norm_map,norm_star,e.norm_map] using
      (e.symm (star (e f))).le_opNorm z
  refine ⟨L.mkContinuous 1 hb,?_,fun a z => hP z a⟩
  exact LinearMap.mkContinuous_norm_le _ zero_le_one hb

 

theorem abstract_multiplication_normal :
    (∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a)) ∧
    (∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a)) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  exact ⟨mul_hasPreadjoint e,mul_right_hasPreadjoint e⟩

end HochschildSakai
end

end OAI
