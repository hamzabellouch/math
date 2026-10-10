import Mathlib
import OAI.Geometry.IntegralFillings.Model
import OAI.Geometry.IntegralFillings.Charts.Reparametrization

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
open Set Metric
open scoped NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C D : IntegerChart X k)
noncomputable def inverseParam (x : X) : Euc k :=
  if hx : x ∈ C.image then (Classical.choose hx : C.domain).val else 0

lemma inverseParam_mem {x : X} (hx : x ∈ C.image) :
    C.inverseParam x ∈ C.domain := by
  simp only [inverseParam,dite_eq_left hx]
  exact (Classical.choose hx).property

lemma param_inverseParam {x : X} (hx : x ∈ C.image) :
    C.param ⟨C.inverseParam x,C.inverseParam_mem hx⟩ = x := by
  change C.param ⟨if h : x ∈ C.image then (Classical.choose h).val else 0,_⟩ = x
  simpa only [dite_eq_left hx] using (Classical.choose_spec hx)

lemma inverseParam_apply (z : C.domain) : C.inverseParam (C.param z) = z := by
  obtain ⟨_,_,_,ha⟩ := C.bilipschitz
  exact congrArg Subtype.val (ha.injective (C.param_inverseParam (show C.param z ∈ C.image from ⟨z,rfl⟩)))

lemma inverseParam_dist {U : ℝ≥0} (ha : AntilipschitzWith U C.param)
    {x y : X} (hx : x ∈ C.image) (hy : y ∈ C.image) :
    dist (C.inverseParam x) (C.inverseParam y) ≤ (U : ℝ) * dist x y := by
  have h := ha.le_mul_dist ⟨C.inverseParam x,C.inverseParam_mem hx⟩
    ⟨C.inverseParam y,C.inverseParam_mem hy⟩
  simpa only [Subtype.dist_eq,C.param_inverseParam hx,C.param_inverseParam hy] using h

noncomputable def transition (z : Euc k) : Euc k :=
  if hz : z ∈ C.domain then D.inverseParam (C.param ⟨z,hz⟩) else 0

lemma transition_apply {z : Euc k} (hz : z ∈ C.domain) :
    C.transition D z = D.inverseParam (C.param ⟨z,hz⟩) := by
  simp only [transition,dite_eq_left hz]

variable (hCD : C.image ⊆ D.image)
include hCD

lemma transition_mem {z : Euc k} (hz : z ∈ C.domain) :
    C.transition D z ∈ D.domain := by
  rw [C.transition_apply D hz]
  exact D.inverseParam_mem (hCD ⟨⟨z,hz⟩,rfl⟩)

lemma transition_param {z : Euc k} (hz : z ∈ C.domain) :
    D.param ⟨C.transition D z,C.transition_mem D hCD hz⟩ = C.param ⟨z,hz⟩ := by
  convert D.param_inverseParam (hCD (show C.param ⟨z,hz⟩ ∈ C.image from ⟨⟨z,hz⟩,rfl⟩)) using 1
  congr 1
  apply Subtype.ext
  exact C.transition_apply D hz

lemma transition_bilipschitz : ∃ K L : ℝ≥0,
    LipschitzOnWith K (C.transition D) C.domain ∧
    ∀ x ∈ C.domain, ∀ y ∈ C.domain,
      dist x y ≤ (L : ℝ) * dist (C.transition D x) (C.transition D y) := by
  obtain ⟨J,U,hJ,hU⟩ := C.bilipschitz
  obtain ⟨K,V,hK,hV⟩ := D.bilipschitz
  refine ⟨V * J,U * K,?_,?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [C.transition_apply D hx,C.transition_apply D hy]
    have h := D.inverseParam_dist hV (hCD ⟨⟨x,hx⟩,rfl⟩) (hCD ⟨⟨y,hy⟩,rfl⟩)
    exact h.trans (by simpa only [NNReal.coe_mul,mul_assoc,Subtype.dist_eq] using
      mul_le_mul_of_nonneg_left (hJ.dist_le_mul ⟨x,hx⟩ ⟨y,hy⟩) V.coe_nonneg)
  · intro x hx y hy
    have h := hU.le_mul_dist ⟨x,hx⟩ ⟨y,hy⟩
    have h' := hK.dist_le_mul ⟨C.transition D x,C.transition_mem D hCD hx⟩
      ⟨C.transition D y,C.transition_mem D hCD hy⟩
    rw [C.transition_param D hCD hx,C.transition_param D hCD hy] at h'
    exact h.trans (by simpa only [NNReal.coe_mul,mul_assoc,Subtype.dist_eq] using
      mul_le_mul_of_nonneg_left h' U.coe_nonneg)

theorem exists_inCoordinates :
    ∃ E : IntegerChart X k, ∃ hED : E.domain ⊆ D.domain,
      (∀ z : E.domain, E.param z = D.param ⟨z,hED z.property⟩) ∧
      E.action = C.action ∧ E.image = C.image := by
  obtain ⟨K,L,hf,ha⟩ := C.transition_bilipschitz D hCD
  let E := C.reparam (C.transition D) hf ha
  have hED : E.domain ⊆ D.domain := by
    rintro y ⟨x,hx,rfl⟩
    exact C.transition_mem D hCD hx
  refine ⟨E,hED,?_,C.reparam_action _ hf ha,C.reparam_image _ hf ha⟩
  intro z
  let x := Function.invFunOn (C.transition D) C.domain z
  have hx : x ∈ C.domain := Function.invFunOn_mem z.property
  have he : C.transition D x = z := Function.invFunOn_eq z.property
  change C.param ⟨x,hx⟩ = D.param ⟨z,hED z.property⟩
  rw [←C.transition_param D hCD hx]
  congr 1
  exact Subtype.ext he

end IntegerChart
end SharpIntegralFillings

end

end OAI
