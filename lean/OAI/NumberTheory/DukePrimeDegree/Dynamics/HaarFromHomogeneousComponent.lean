import OAI.NumberTheory.DukePrimeDegree.Dynamics.OpenSubgroupOrbit
import OAI.NumberTheory.PrimePackets.RootSubgroups

namespace OAI

/-!
# From one homogeneous component to prime-degree Haar rigidity

The orbit measure may be one component of the ambient measure, and its
orbit group may be disconnected. The finite-dimensional and arithmetic
arguments identify Haar probability from a finite-volume component with
an A-normalized group containing the invariant roots.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The finite-volume orbit consequence, without connectedness or an
extra finite-volume hypothesis for the root-generated group. -/
theorem root_partition_universal_of_maximal_roots_and_orbit {n : ℕ}
    (hn : n.Prime) (g : G n) (L : Subgroup (G n))
    (hclosed : IsClosed (L : Set (G n)))
    (hnormal : ∀ (ell : Fin n → ℝ) (hsum : ∑ a, ell a = 0) (t : ℝ),
      ∀ h ∈ L, diagonalOneParameter ell hsum t * h * diagonalOneParameter ell hsum (-t) ∈ L)
    (r : Setoid (Fin n)) (hnontrivial : ∃ i j, i ≠ j ∧ r i j)
    (hmax : ∀ (a b : Fin n) (hab : a ≠ b) (c : ℝ), c ≠ 0 →
      Matrix.SpecialLinearGroup.transvection hab c ∈ L → r a b)
    (hroot : ∀ i j (hij : i ≠ j), r i j →
      Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (ν : Measure (X n)) [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (horbit : ∀ᵐ x ∂ν, x ∈ range (latticeOrbitPoint g L))
    (hinv : ∀ h : L, ν.map (fun x => rightAction x h.val) = ν)
    (hgeneric : ∀ᵐ x ∂ν, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0) :
    ∀ i j, r i j :=
  root_partition_universal_of_open_blockSubgroup_orbit hn g L hclosed r hnontrivial
    (blockIntersection_isOpen_of_maximal_roots L hclosed hnormal r hmax)
    hroot ν hν horbit hinv hgeneric

/-- A single actual homogeneous component suffices to make an ambient
A-invariant probability measure Haar, once its nontrivial invariant-root
partition and the homogeneous group's invariance are known. -/
theorem isHaar_of_prime_homogeneous_component
    (d : ℕ) (hprime : (d + 1).Prime)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (r : Setoid (Fin (d + 1)))
    (hr : ∀ i j, r i j ↔ rootInvarianceRelation μ i j)
    (hnontrivial : ∃ i j, i ≠ j ∧ r i j)
    (g : G (d + 1)) (L : Subgroup (G (d + 1)))
    (hclosed : IsClosed (L : Set (G (d + 1))))
    (hnormal : ∀ (ell : Fin (d + 1) → ℝ) (hsum : ∑ a, ell a = 0) (t : ℝ),
      ∀ h ∈ L, diagonalOneParameter ell hsum t * h * diagonalOneParameter ell hsum (-t) ∈ L)
    (hLμ : L ≤ invariantRightSubgroup μ)
    (hroot : ∀ i j (hij : i ≠ j), r i j →
      Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (ν : Measure (X (d + 1))) [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (horbit : ∀ᵐ x ∂ν, x ∈ range (latticeOrbitPoint g L))
    (hinv : ∀ h : L, ν.map (fun x => rightAction x h.val) = ν)
    (hgeneric : ∀ᵐ x ∂ν, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0) :
    IsHaarProbability μ := by
  have hmax : ∀ (a b : Fin (d + 1)) (hab : a ≠ b) (c : ℝ), c ≠ 0 →
      Matrix.SpecialLinearGroup.transvection hab c ∈ L → r a b := by
    intro a b hab c hc hmem
    apply (hr a b).mpr
    right
    refine ⟨hab, ?_⟩
    exact root_mem_of_nonzero_parameter (invariantRightSubgroup μ) hA hab hc (hLμ hmem)
  have hall := root_partition_universal_of_maximal_roots_and_orbit hprime g L hclosed
    hnormal r hnontrivial hmax hroot ν hν horbit hinv hgeneric
  refine ⟨inferInstance, right_invariant_of_all_roots (by have := hprime.two_le; omega) μ ?_⟩
  intro i j hij t
  rcases (hr i j).mp (hall i j) with heq | ⟨_, h⟩
  · exact (hij heq).elim
  · exact h t

end DukePrimeDegree

end

end OAI
