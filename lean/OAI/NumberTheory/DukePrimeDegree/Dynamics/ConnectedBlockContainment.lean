import OAI.NumberTheory.DukePrimeDegree.Dynamics.GenericBlockOrbit
import Mathlib.Topology.Algebra.OpenSubgroup

namespace OAI

/-!
# Local block preservation implies global preservation

Conjugates of coordinate projections detect the off-block entries of a
matrix close to the identity. For a connected subgroup, this local
condition gives containment in the actual block-diagonal subgroup.
The next root-extraction argument supplies the projection identities.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- An open neighborhood of the identity in a subgroup is enough for
containment in another subgroup when the first group is connected. -/
theorem subgroup_le_of_mem_nhds_one {n : ℕ}
    (L K : Subgroup (G n)) [PreconnectedSpace L]
    (hlocal : {g : L | g.val ∈ K} ∈ 𝓝 (1 : L)) : L ≤ K := by
  let S := K.comap L.subtype
  have hopen : IsOpen (S : Set L) := S.isOpen_of_mem_nhds hlocal
  have he : (S : Set L) = univ :=
    (IsClopen.eq_univ ⟨S.isClosed_of_isOpen hopen, hopen⟩ ⟨1, S.one_mem⟩)
  intro g hg
  have hm : (⟨g, hg⟩ : L) ∈ S := by
    change (⟨g, hg⟩ : L) ∈ (S : Set L)
    rw [he]
    trivial
  exact hm

/-- Conjugated coordinate projections force block preservation on an
open neighborhood inside L, without a connectedness assumption. -/
theorem blockIntersection_mem_nhds_one_of_projection_products {n : ℕ}
    (L : Subgroup (G n)) (r : Setoid (Fin n))
    (hproducts : ∀ g : L, ∀ a b, ¬ r a b → ∀ k,
      g.val.val a k * g.val⁻¹.val k b = 0) :
    {g : L | g.val ∈ blockMatrixGroup r} ∈ 𝓝 (1 : L) := by
  have hopen : IsOpen {g : L | ∀ j, g.val⁻¹.val j j ≠ 0} := by
    have heq : {g : L | ∀ j, g.val⁻¹.val j j ≠ 0} =
        ⋂ j : Fin n, {g : L | g.val⁻¹.val j j ≠ 0} := by ext g; simp
    rw [heq]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_ne.preimage (by fun_prop)
  have hone : (1 : L) ∈ {g : L | ∀ j, g.val⁻¹.val j j ≠ 0} := by
    intro j
    simp
  apply Filter.mem_of_superset (hopen.mem_nhds hone)
  intro g hg
  have hz : ∀ a b, ¬ r a b → g.val.val a b = 0 := by
    intro a b hab
    exact (mul_eq_zero.mp (hproducts g a b hab b)).resolve_right (hg b)
  have hcomm := (commute_blockScalars_iff r g.val.val).mpr hz
  intro c hc
  apply slMatrixConjugation_eq_self
  apply Commute.symm
  apply hcomm
  apply (mem_blockScalarAlgebra_iff r _).mpr
  refine ⟨by simp, ?_⟩
  intro i j hij
  simpa only [Matrix.diagonal_apply_eq] using hc i j hij

/-- The subgroup preserving the blocks is open in L. -/
theorem blockIntersection_isOpen_of_projection_products {n : ℕ}
    (L : Subgroup (G n)) (r : Setoid (Fin n))
    (hproducts : ∀ g : L, ∀ a b, ¬ r a b → ∀ k,
      g.val.val a k * g.val⁻¹.val k b = 0) :
    IsOpen (((blockMatrixGroup r).comap L.subtype : Subgroup L) : Set L) :=
  Subgroup.isOpen_of_mem_nhds _
    (blockIntersection_mem_nhds_one_of_projection_products L r hproducts)

/-- The polynomial identities on conjugated coordinate projections
force block preservation everywhere in a connected subgroup. -/
theorem connected_subgroup_le_blocks_of_projection_products {n : ℕ}
    (L : Subgroup (G n)) [PreconnectedSpace L] (r : Setoid (Fin n))
    (hproducts : ∀ g : L, ∀ a b, ¬ r a b → ∀ k,
      g.val.val a k * g.val⁻¹.val k b = 0) : L ≤ blockMatrixGroup r :=
  subgroup_le_of_mem_nhds_one L (blockMatrixGroup r)
    (blockIntersection_mem_nhds_one_of_projection_products L r hproducts)

end DukePrimeDegree

end

end OAI
