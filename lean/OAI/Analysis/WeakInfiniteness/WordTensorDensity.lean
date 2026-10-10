import Mathlib
import OAI.Analysis.WeakInfiniteness.AlgebraicTensorSpan
import OAI.Analysis.WeakInfiniteness.PolynomialSpan
import OAI.Analysis.WeakInfiniteness.TensorFunctoriality

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

lemma universal_word_span_dense (S : Submodule ℂ UniversalContraction)
    (hS : IsClosed (S : Set UniversalContraction)) (hw : ∀ w, universalWord w ∈ S) :
    S = ⊤ := by
  let f : UniversalContraction →⋆ₐ[ℂ] ContractionAmbient := universalContractionSubalgebra.subtype
  let T : Submodule ℂ ContractionAmbient := S.map f.toLinearMap
  have hT : IsClosed (T : Set ContractionAmbient) :=
    (closedStarSpan_closed {universalOperator}).isClosedMap_subtype_val _ hS
  have hp : ∀ c : List Bool →₀ ℂ, algebraPolynomial universalContractionGenerator c ∈ S := by
    intro c
    unfold algebraPolynomial
    apply S.sum_mem
    intro w _hw
    exact S.smul_mem _ (algebraWord_universal w ▸ hw w)
  have ha : (StarAlgebra.adjoin ℂ {universalOperator} : Set ContractionAmbient) ⊆ T := by
    intro y hy
    obtain ⟨c, rfl⟩ := exists_polynomial_of_mem_adjoin universalOperator y hy
    let z : UniversalContraction := algebraPolynomial universalContractionGenerator c
    refine ⟨z, hp c, ?_⟩
    exact map_algebraPolynomial f universalContractionGenerator c
  apply top_unique
  intro x _hx
  have hxT : x.val ∈ T := (closure_minimal ha hT) x.property
  obtain ⟨y, hy, he⟩ := hxT
  have hey : y = x := Subtype.ext he
  exact hey ▸ hy

section TensorDensity

variable {A : Type*} {C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C]

def minimalElementaryRightLinear (a : A) : C →ₗ[ℂ] MinimalTensor A C where
  toFun := minimalElementary a
  map_add' c d := Subtype.ext (spatialElementary_add_right a c d)
  map_smul' r c := Subtype.ext (spatialElementary_smul_right r a c)

def minimalElementaryLeftLinear (c : C) : A →ₗ[ℂ] MinimalTensor A C where
  toFun a := minimalElementary a c
  map_add' a b := Subtype.ext (spatialElementary_add_left a b c)
  map_smul' r a := Subtype.ext (spatialElementary_smul_left r a c)

def minimalElementaryRightContinuous (a : A) : C →L[ℂ] MinimalTensor A C :=
  (minimalElementaryRightLinear a).mkContinuous ‖a‖ (norm_spatialElementary_le a)

def minimalElementaryLeftContinuous (c : C) : A →L[ℂ] MinimalTensor A C :=
  (minimalElementaryLeftLinear c).mkContinuous ‖c‖ (fun a => by
    change ‖spatialElementary a c‖ ≤ ‖c‖ * ‖a‖
    simpa only [mul_comm] using norm_spatialElementary_le a c)

lemma minimal_elementary_span_dense (S : Submodule ℂ (MinimalTensor A C))
    (hS : IsClosed (S : Set (MinimalTensor A C)))
    (he : ∀ a c, minimalElementary a c ∈ S) : S = ⊤ := by
  let T : Submodule ℂ (SpatialAmbient A C) :=
    S.map (minimalTensorSubalgebra A C).toSubmodule.subtype
  have hT : IsClosed (T : Set (SpatialAmbient A C)) :=
    isClosed_closure.isClosedMap_subtype_val _ hS
  have hs : Submodule.span ℂ
      (Set.range fun p : A × C => spatialElementary p.1 p.2) ≤ T := by
    apply Submodule.span_le.mpr
    rintro y ⟨⟨a,c⟩,rfl⟩
    exact ⟨minimalElementary a c, he a c, rfl⟩
  apply top_unique
  intro x _hx
  have hx' := x.property
  change x.val ∈ (minimalTensorSubalgebra A C : Set (SpatialAmbient A C)) at hx'
  rw [minimalTensor_eq_closure_span] at hx'
  have hxT : x.val ∈ T := (closure_minimal hs hT) hx'
  obtain ⟨y,hy,he⟩ := hxT
  have he' : y = x := Subtype.ext he
  exact he' ▸ hy

end TensorDensity

variable {C : Type*} [NonUnitalCStarAlgebra C]

def wordTensorLinear : (List Bool →₀ C) →ₗ[ℂ] MinimalTensor UniversalContraction C :=
  Finsupp.lsum ℂ (fun w => minimalElementaryRightLinear (universalWord w))

lemma wordTensorLinear_apply (c : List Bool →₀ C) :
    wordTensorLinear c = ∑ w ∈ c.support, minimalElementary (universalWord w) (c w) := rfl

lemma wordTensorLinear_range_dense : DenseRange (wordTensorLinear (C := C)) := by
  have hd : (LinearMap.range (wordTensorLinear (C := C))).topologicalClosure = ⊤ := by
    apply minimal_elementary_span_dense _ (Submodule.isClosed_topologicalClosure _)
    intro a c
    let S : Submodule ℂ UniversalContraction :=
      (LinearMap.range (wordTensorLinear (C := C))).topologicalClosure.comap
        (minimalElementaryLeftLinear c)
    have hS : IsClosed (S : Set UniversalContraction) :=
      (Submodule.isClosed_topologicalClosure _).preimage (minimalElementaryLeftContinuous c).continuous
    have hw : ∀ w, universalWord w ∈ S := by
      intro w
      apply Submodule.le_topologicalClosure
      refine ⟨Finsupp.single w c, ?_⟩
      exact Finsupp.lsum_single ℂ (fun w => minimalElementaryRightLinear (universalWord w)) w c
    have hall := universal_word_span_dense S hS hw
    have ha : a ∈ S := by rw [hall]; trivial
    exact ha
  apply dense_iff_closure_eq.mpr
  exact congrArg (fun S : Submodule ℂ (MinimalTensor UniversalContraction C) => (S : Set (MinimalTensor UniversalContraction C))) hd

end

end WeakPureInfiniteness
end

end OAI
