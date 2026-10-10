import Mathlib
import OAI.Analysis.WeakInfiniteness.AlgebraicTensorSpan
import OAI.Analysis.WeakInfiniteness.GroupPolynomials
import OAI.Analysis.WeakInfiniteness.TensorFunctoriality

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

universe u v

section TensorContinuity

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def spatialElementaryLeft (b : B) : A →L[ℂ] SpatialAmbient A B :=
  LinearMap.mkContinuous
    { toFun a := spatialElementary a b
      map_add' a a' := spatialElementary_add_left a a' b
      map_smul' c a := spatialElementary_smul_left c a b }
    ‖b‖ (fun a => by
      change ‖spatialElementary a b‖ ≤ ‖b‖ * ‖a‖
      simpa only [mul_comm ‖b‖] using norm_spatialElementary_le a b)

def spatialElementaryRight (a : A) : B →L[ℂ] SpatialAmbient A B :=
  LinearMap.mkContinuous
    { toFun b := spatialElementary a b
      map_add' b b' := spatialElementary_add_right a b b'
      map_smul' c b := spatialElementary_smul_right c a b }
    ‖a‖ (norm_spatialElementary_le a)

@[simp] lemma spatialElementaryLeft_apply (a : A) (b : B) :
    spatialElementaryLeft b a = spatialElementary a b := rfl

@[simp] lemma spatialElementaryRight_apply (a : A) (b : B) :
    spatialElementaryRight a b = spatialElementary a b := rfl

lemma spatialElementary_sum_left {I : Type*} (s : Finset I) (a : I → A) (b : B) :
    spatialElementary (∑ i ∈ s, a i) b = ∑ i ∈ s, spatialElementary (a i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, spatialElementary_add_left, ih]

lemma spatialElementary_sum_right {I : Type*} (s : Finset I) (a : A) (b : I → B) :
    spatialElementary a (∑ i ∈ s, b i) = ∑ i ∈ s, spatialElementary a (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, spatialElementary_add_right, ih]

def minimalAmbientInclusion : MinimalTensor A B →⋆ₙₐ[ℂ] SpatialAmbient A B where
  toFun x := x.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

end TensorContinuity

section GroupTensorDensity

variable {G : Type u} [Group G]

def groupTensorPolynomial : (G × G →₀ ℂ) →ₗ[ℂ]
    MinimalTensor (FullGroupAlgebra G) (FullGroupAlgebra G) :=
  Finsupp.linearCombination ℂ (fun p => minimalElementary (fullGroupElement p.1) (fullGroupElement p.2))

lemma groupTensorPolynomial_val (c : G × G →₀ ℂ) :
    (groupTensorPolynomial c).val = c.sum (fun p z => z •
      spatialElementary (fullGroupElement p.1) (fullGroupElement p.2)) := by
  simp only [groupTensorPolynomial, Finsupp.linearCombination_apply, Finsupp.sum]
  change (minimalAmbientInclusion (A := FullGroupAlgebra G) (B := FullGroupAlgebra G))
    (∑ p ∈ c.support, c p • minimalElementary (fullGroupElement p.1) (fullGroupElement p.2)) = _
  simp only [map_sum, map_smul]
  rfl

lemma groupTensorPolynomial_dense : DenseRange (groupTensorPolynomial (G := G)) := by
  let S : Submodule ℂ (SpatialAmbient (FullGroupAlgebra G) (FullGroupAlgebra G)) :=
    Submodule.span ℂ (Set.range fun p : G × G =>
      spatialElementary (fullGroupElement p.1) (fullGroupElement p.2))
  have hgen (s t : G) : spatialElementary (fullGroupElement s) (fullGroupElement t) ∈ S :=
    Submodule.subset_span (Set.mem_range_self (s,t))
  have hpoly (c d : G →₀ ℂ) :
      spatialElementary (fullGroupPolynomial c) (fullGroupPolynomial d) ∈ S := by
    change spatialElementary (c.sum (fun s z => z • fullGroupElement s))
      (d.sum (fun t z => z • fullGroupElement t)) ∈ S
    have hl := spatialElementary_sum_left (A := FullGroupAlgebra G) (B := FullGroupAlgebra G)
      c.support (fun s => c s • fullGroupElement s) (d.sum (fun t z => z • fullGroupElement t))
    refine hl.symm ▸ ?_
    apply Submodule.sum_mem S
    intro s hs
    have hsm := spatialElementary_smul_left (A := FullGroupAlgebra G) (B := FullGroupAlgebra G)
      (c s) (fullGroupElement s) (d.sum (fun t z => z • fullGroupElement t))
    refine hsm.symm ▸ ?_
    apply Submodule.smul_mem S
    have hr := spatialElementary_sum_right (A := FullGroupAlgebra G) (B := FullGroupAlgebra G)
      d.support (fullGroupElement s) (fun t => d t • fullGroupElement t)
    refine hr.symm ▸ ?_
    apply Submodule.sum_mem S
    intro t ht
    have hsm' := spatialElementary_smul_right (A := FullGroupAlgebra G) (B := FullGroupAlgebra G)
      (d t) (fullGroupElement s) (fullGroupElement t)
    exact hsm'.symm ▸ Submodule.smul_mem S _ (hgen s t)
  have hall (a b : FullGroupAlgebra G) : spatialElementary a b ∈ S.topologicalClosure := by
    refine (fullGroupPolynomial_dense (G := G)).induction_on a ?_ ?_
    · exact S.isClosed_topologicalClosure.preimage (spatialElementaryLeft b).continuous
    · intro c
      refine (fullGroupPolynomial_dense (G := G)).induction_on b ?_ ?_
      · exact S.isClosed_topologicalClosure.preimage (spatialElementaryRight (fullGroupPolynomial c)).continuous
      · intro d
        exact Submodule.le_topologicalClosure S (hpoly c d)
  have hr (x : MinimalTensor (FullGroupAlgebra G) (FullGroupAlgebra G)) : x.val ∈ S.topologicalClosure := by
    have hx : x.val ∈ (minimalTensorSubalgebra (FullGroupAlgebra G) (FullGroupAlgebra G) : Set _) := x.property
    rw [minimalTensor_eq_closure_span] at hx
    exact closure_minimal (Submodule.span_le.mpr (by rintro _ ⟨⟨a,b⟩,rfl⟩; exact hall a b))
      S.isClosed_topologicalClosure hx
  rw [Metric.denseRange_iff]
  intro x ε hε
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp (hr x) ε hε
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
  refine ⟨c, ?_⟩
  rw [dist_eq_norm]
  change ‖x.val - (groupTensorPolynomial c).val‖ < ε
  rw [groupTensorPolynomial_val]
  simpa only [dist_eq_norm] using hd

end GroupTensorDensity

end WeakPureInfiniteness
end

end OAI
