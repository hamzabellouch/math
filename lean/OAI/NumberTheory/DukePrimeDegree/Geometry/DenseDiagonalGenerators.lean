import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.Constructions.DomMulAct

namespace OAI

/-!
# A finite dense generating family for diagonal parameters

In each real logarithmic coordinate, shifts by one and by square root
of two generate a dense additive subgroup. Thus the diagonal action
has a concrete finite topologically generating family; no one of its
elements is asserted to be ergodic.
-/

noncomputable section
open Set
open scoped BigOperators

namespace DukePrimeDegree

variable {I : Type*} [Fintype I] [DecidableEq I]

def diagonalParameterGenerators (p : I × Bool) : I → ℝ :=
  Pi.single p.1 (if p.2 then Real.sqrt 2 else 1)

def singleCoordinateAddHom (i : I) : ℝ →+ (I → ℝ) where
  toFun := fun t : ℝ => (Pi.single i t : I → ℝ)
  map_zero' := by ext j; simp
  map_add' s t := by ext j; by_cases h : i = j <;> simp [h]

omit [Fintype I] in
lemma continuous_singleCoordinateAddHom (i : I) :
    Continuous (singleCoordinateAddHom i : ℝ → I → ℝ) := by
  apply continuous_pi
  intro j
  by_cases h : i = j
  · subst j
    have he : (fun t : ℝ => singleCoordinateAddHom i t i) = id := by
      funext t
      simp [singleCoordinateAddHom]
    change Continuous (fun t : ℝ => singleCoordinateAddHom i t i)
    rw [he]
    exact continuous_id
  · simpa [singleCoordinateAddHom, h] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

theorem dense_diagonalParameterGenerators :
    Dense (AddSubgroup.closure (range (diagonalParameterGenerators (I := I))) : Set (I → ℝ)) := by
  let H := AddSubgroup.closure (range (diagonalParameterGenerators (I := I)))
  have hline (i : I) (t : ℝ) : Pi.single i t ∈ H.topologicalClosure := by
    let S : AddSubgroup ℝ := H.topologicalClosure.comap (singleCoordinateAddHom i)
    have hSclosed : IsClosed (S : Set ℝ) :=
      H.isClosed_topologicalClosure.preimage (continuous_singleCoordinateAddHom i)
    have h1 : (1 : ℝ) ∈ S := by
      apply H.le_topologicalClosure
      apply AddSubgroup.subset_closure
      exact ⟨(i, false), by simp [diagonalParameterGenerators, singleCoordinateAddHom]⟩
    have h2 : Real.sqrt 2 ∈ S := by
      apply H.le_topologicalClosure
      apply AddSubgroup.subset_closure
      exact ⟨(i, true), by simp [diagonalParameterGenerators, singleCoordinateAddHom]⟩
    have hd : Dense (AddSubgroup.closure {Real.sqrt 2, 1} : Set ℝ) :=
      dense_addSubgroupClosure_pair_iff.mpr (by simpa using irrational_sqrt_two)
    have hle : AddSubgroup.closure {Real.sqrt 2, 1} ≤ S :=
      (AddSubgroup.closure_le _).mpr (by rw [pair_subset_iff]; exact ⟨h2, h1⟩)
    have hdS : Dense (S : Set ℝ) := hd.mono hle
    have ht : t ∈ (S : Set ℝ) := by
      rw [← hSclosed.closure_eq]
      exact hdS t
    exact ht
  intro v
  change v ∈ closure (H : Set (I → ℝ))
  change v ∈ H.topologicalClosure
  have he : (∑ i, Pi.single i (v i)) = v := by
    ext j
    simp
  rw [← he]
  exact H.topologicalClosure.sum_mem (fun i _ => hline i (v i))

def multiplicativeParameterGenerators (p : I × Bool) : Multiplicative (I → ℝ) :=
  Multiplicative.ofAdd (diagonalParameterGenerators p)

lemma dense_multiplicativeParameterGenerators :
    Dense (Subgroup.closure (range (multiplicativeParameterGenerators (I := I))) :
      Set (Multiplicative (I → ℝ))) := by
  have he : (AddSubgroup.closure (range (diagonalParameterGenerators (I := I)))).toSubgroup =
      Subgroup.closure (range (multiplicativeParameterGenerators (I := I))) := by
    rw [AddSubgroup.toSubgroup_closure]
    congr 1
  rw [← he]
  exact dense_diagonalParameterGenerators

/-- On an abelian group the domain-action type tag is also a group
homomorphism, so dense generators transfer to the Koopman action. -/
def parameterDomainHom : Multiplicative (I → ℝ) →*
    (Multiplicative (I → ℝ))ᵈᵐᵃ where
  toFun := DomMulAct.mk
  map_one' := rfl
  map_mul' g h := by rw [DomMulAct.mk_mul, mul_comm]

def domainParameterGenerators (p : I × Bool) : (Multiplicative (I → ℝ))ᵈᵐᵃ :=
  parameterDomainHom (multiplicativeParameterGenerators p)

theorem dense_domainParameterGenerators :
    Dense (Subgroup.closure (range (domainParameterGenerators (I := I))) :
      Set (Multiplicative (I → ℝ))ᵈᵐᵃ) := by
  have he : (Subgroup.closure (range (multiplicativeParameterGenerators (I := I)))).map
      parameterDomainHom = Subgroup.closure (range (domainParameterGenerators (I := I))) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [← he, Subgroup.coe_map]
  have hd : DenseRange (parameterDomainHom (I := I)) := DomMulAct.mk.surjective.denseRange
  exact hd.dense_image DomMulAct.continuous_mk dense_multiplicativeParameterGenerators

end DukePrimeDegree

end

end OAI
