import Mathlib
import OAI.Analysis.WeakInfiniteness.FullGroupDensity

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

variable {G : Type*} [Group G]

def fullGroupAmbientInclusion : FullGroupAlgebra G →⋆ₐ[ℂ] FullGroupAmbient G where
  toFun x := x.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_one' := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def fullGroupPolynomial : (G →₀ ℂ) →ₗ[ℂ] FullGroupAlgebra G :=
  Finsupp.linearCombination ℂ fullGroupElement

lemma fullGroupPolynomial_val (c : G →₀ ℂ) :
    (fullGroupPolynomial c).val = c.sum (fun g z => z • fullGroupOperator g) := by
  simp only [fullGroupPolynomial, Finsupp.linearCombination_apply, Finsupp.sum]
  change (fullGroupAmbientInclusion (G := G)) (∑ g ∈ c.support, c g • fullGroupElement g) = _
  simp only [map_sum, map_smul]
  rfl

lemma fullGroupPolynomial_dense : DenseRange (fullGroupPolynomial (G := G)) := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  have hx : x.val ∈ (fullGroupSubalgebra G : Set (FullGroupAmbient G)) := x.property
  rw [fullGroupSubalgebra_eq_closure_span] at hx
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hx ε hε
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
  refine ⟨c, ?_⟩
  rw [dist_eq_norm]
  change ‖x.val - (fullGroupPolynomial c).val‖ < ε
  rw [fullGroupPolynomial_val]
  simpa only [dist_eq_norm] using hdist

end WeakPureInfiniteness
end

end OAI
