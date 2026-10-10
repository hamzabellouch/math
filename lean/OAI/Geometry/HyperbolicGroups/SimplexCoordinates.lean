import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedron

namespace OAI

section


/-! Explicit finite simplex coordinates, with the actual barycentric subspace
topology. No CW coordinate comparison is assumed. -/
noncomputable section
open scoped Topology
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [DecidableEq V] {n : ℕ}

def barycentric (e : Fin n → V) (z : Fin n → ℝ) : V → ℝ := fun j =>
  ∑ i, if e i = j then z i else 0

lemma barycentric_continuous (e : Fin n → V) : Continuous (barycentric e) := by
  apply continuous_pi
  intro j
  unfold barycentric
  apply continuous_finsetSum
  intro i hi
  split_ifs <;> fun_prop

lemma barycentric_at {e : Fin n → V} (he : Function.Injective e)
    (z : Fin n → ℝ) (i : Fin n) : barycentric e z (e i) = z i := by
  simp [barycentric,he.eq_iff]
lemma barycentric_off {e : Fin n → V} (z : Fin n → ℝ) {j : V}
    (hj : j ∉ Finset.univ.image e) : barycentric e z j = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  exact ite_eq_right (fun h => hj (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,h⟩))

variable [Fintype V]

lemma barycentric_sum (e : Fin n → V) (z : Fin n → ℝ) :
    ∑ j, barycentric e z j = ∑ i, z i := by
  simp [barycentric,Finset.sum_comm]

lemma barycentric_mem (e : Fin n → V)
    (z : {weights : Fin n → ℝ // (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}) :
    barycentric e z ∈ simplex (Finset.univ.image e) := by
  refine ⟨fun j => Finset.sum_nonneg (fun i hi => ?_),?_,?_⟩
  · split_ifs <;> first | exact z.property.1 i | exact le_refl 0
  · exact (barycentric_sum e z).trans z.property.2
  · exact fun j hj => barycentric_off z.val hj

lemma barycentric_read {e : Fin n → V} (he : Function.Injective e)
    (x : simplex (Finset.univ.image e)) :
    barycentric e (fun i => x.val (e i)) = x.val := by
  funext j
  by_cases hj : j ∈ Finset.univ.image e
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact barycentric_at he _ i
  · rw [barycentric_off _ hj,x.property.2.2 j hj]

/-- Canonical homeomorphism to a closed simplex with distinct vertices `e`. -/
def simplexCoordinates {e : Fin n → V} (he : Function.Injective e) :
    {weights : Fin n → ℝ // (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1} ≃ₜ
      simplex (Finset.univ.image e) where
  toFun z := ⟨barycentric e z,barycentric_mem e z⟩
  invFun x := ⟨fun i => x.val (e i),fun i => x.property.1 (e i),by
    rw [←barycentric_sum e (fun i => x.val (e i)),barycentric_read he x]
    exact x.property.2.1⟩
  left_inv z := by apply Subtype.ext; funext i; exact barycentric_at he z i
  right_inv x := Subtype.ext (barycentric_read he x)
  continuous_toFun := ((barycentric_continuous e).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => (continuous_apply (e i)).comp continuous_subtype_val

variable (K : AbstractSimplicialComplex V)
/-- The closed simplex in the carrier and its ambient barycentric subtype
carry exactly the same topology. -/
def closedSimplexHomeomorph {s : Finset V} (hs : s ∈ K.faces) :
    simplex s ≃ₜ {x : Carrier K // x.val ∈ simplex s} where
  toFun x := ⟨⟨x.val,simplex_subset_carrier K hs x.property⟩,x.property⟩
  invFun x := ⟨x.val.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

end HyperbolicObstruction.FinitePolyhedron
end
end

section

end

end OAI
