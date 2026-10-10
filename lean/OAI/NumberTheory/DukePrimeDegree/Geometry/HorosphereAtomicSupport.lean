import OAI.NumberTheory.DukePrimeDegree.Geometry.AtomicRootLimits
import OAI.NumberTheory.DukePrimeDegree.Geometry.HorosphereIsolatedLimit
import OAI.NumberTheory.DukePrimeDegree.Geometry.HorosphereRootExtraction
import OAI.NumberTheory.DukePrimeDegree.Entropy.LowEntropySupportReduction

namespace OAI

/-!
# The atomic horospherical support theorem

This proves the support conclusion used in EKL (2006), Lemma 4.4(1).
For each peripheral root, an explicit diagonal flow isolates its matrix
entry. Atomicity and compact recurrence force that entry to vanish.
Thus only the distinguished root remains. This argument establishes the
needed consequence directly, without assuming the general product
formula of Einsiedler–Katok (2003), Proposition 8.3.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_nullset_horospherical_root_support
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hrow : ∀ (k : Fin (d + 1)) (hki : k ≠ i), k ≠ j →
      ∀ᵐ x ∂μ, intrinsicRootLeaf hki.symm μ x = Measure.dirac 0)
    (hcol : ∀ k : Fin (d + 1), k ≠ i → (hkj : k ≠ j) →
      ∀ᵐ x ∂μ, intrinsicRootLeaf hkj μ x = Measure.dirac 0) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ x ∉ N, ∀ g : G (d + 1), RootHorosphereShape i j g → rightAction x g ∉ N →
        g = Matrix.SpecialLinearGroup.transvection hij (g.val i j) := by
  let I := {k : Fin (d + 1) // k ≠ i ∧ k ≠ j}
  have hr (k : I) := exists_nullset_atomic_root_limit d k.prop.1.symm μ hA
    (hrow k.val k.prop.1 k.prop.2) (centerWeights d (rowIsolatingRaw i j k.val))
    (centerWeights_sum d _)
  have hc (k : I) := exists_nullset_atomic_root_limit d k.prop.2 μ hA
    (hcol k.val k.prop.1 k.prop.2) (centerWeights d (columnIsolatingRaw i j k.val))
    (centerWeights_sum d _)
  choose R hR hRzero hRlimit using hr
  choose C hC hCzero hClimit using hc
  let N := (⋃ k : I, R k) ∪ ⋃ k : I, C k
  refine ⟨N, (MeasurableSet.iUnion hR).union (MeasurableSet.iUnion hC),
    measure_union_null (measure_iUnion_null hRzero) (measure_iUnion_null hCzero), ?_⟩
  intro x hx g hg hxg
  apply rootHorosphere_eq_transvection_of_peripheral_zero hij g hg
  · intro k hki hkj
    let q : I := ⟨k, hki, hkj⟩
    have hxR : x ∉ R q := fun h => hx (Or.inl (mem_iUnion.mpr ⟨q, h⟩))
    have hyR : rightAction x g ∉ R q := fun h => hxg (Or.inl (mem_iUnion.mpr ⟨q, h⟩))
    exact hRlimit q x hxR (rightAction x g) hyR g rfl (g.val i k)
      (horosphere_row_root_limit d hij hki.symm hkj g hg)
  · intro k hki hkj
    let q : I := ⟨k, hki, hkj⟩
    have hxC : x ∉ C q := fun h => hx (Or.inr (mem_iUnion.mpr ⟨q, h⟩))
    have hyC : rightAction x g ∉ C q := fun h => hxg (Or.inr (mem_iUnion.mpr ⟨q, h⟩))
    exact hClimit q x hxC (rightAction x g) hyC g rfl (g.val k j)
      (horosphere_column_root_limit d hij hki hkj g hg)

end DukePrimeDegree

end

end OAI
