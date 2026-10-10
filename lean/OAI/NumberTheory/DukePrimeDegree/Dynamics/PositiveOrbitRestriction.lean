import OAI.NumberTheory.DukePrimeDegree.Dynamics.HaarFromHomogeneousComponent
import OAI.NumberTheory.DukePrimeDegree.Dynamics.NormalizerOrbitReduction
import OAI.NumberTheory.DukePrimeDegree.Dynamics.InvariantMeasureGroup

namespace OAI

/-!
# A positive-mass orbit supplies the finite homogeneous measure

No homogeneous decomposition is needed once a single orbit of the
actual measure stabilizer has positive mass: restriction to that orbit
is a nonzero finite invariant measure. The resulting orbit obstruction
identifies Haar probability from the stated positive-orbit hypothesis.
-/

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The existing invariant subgroup itself can be used as the orbit
group. Thus one positive-mass orbit is enough for the arithmetic
prime-degree obstruction, with no decomposition or orbit measure added
as another premise. -/
theorem isHaar_of_positive_invariantSubgroup_orbit
    (d : ℕ) (hprime : (d + 1).Prime)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (r : Setoid (Fin (d + 1)))
    (hr : ∀ i j, r i j ↔ rootInvarianceRelation μ i j)
    (hnontrivial : ∃ i j, i ≠ j ∧ r i j)
    (g : G (d + 1))
    (hpos : μ (range (latticeOrbitPoint g (invariantRightSubgroup μ))) ≠ 0) :
    IsHaarProbability μ := by
  let L := invariantRightSubgroup μ
  have hclosed : IsClosed (L : Set (G (d + 1))) := isClosed_invariantRightSubgroup μ
  have hdiag (ell : Fin (d + 1) → ℝ) (hsum : ∑ a, ell a = 0) (t : ℝ) :
      diagonalOneParameter ell hsum t ∈ L := by
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hnormal : ∀ (ell : Fin (d + 1) → ℝ) (hsum : ∑ a, ell a = 0) (t : ℝ),
      ∀ h ∈ L, diagonalOneParameter ell hsum t * h * diagonalOneParameter ell hsum (-t) ∈ L := by
    intro ell hsum t h hh
    exact L.mul_mem (L.mul_mem (hdiag ell hsum t) hh) (hdiag ell hsum (-t))
  have hroot : ∀ i j (hij : i ≠ j), r i j →
      Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L := by
    intro i j hij hijr
    rcases (hr i j).mp hijr with heq | ⟨_hij', hinv⟩
    · exact (hij heq).elim
    · exact hinv 1
  let S := range (latticeOrbitPoint g L)
  have hs : MeasurableSet S :=
    (latticeOrbitPoint_measurableEmbedding g L hclosed).measurableSet_range
  have hν : μ.restrict S ≠ 0 := by
    exact mt Measure.restrict_eq_zero.mp hpos
  exact isHaar_of_prime_homogeneous_component d hprime μ hA r hr hnontrivial
    g L hclosed hnormal le_rfl hroot (μ.restrict S) hν (ae_restrict_mem hs)
    (restrict_orbit_invariant g L hclosed μ (fun h => h.property))
    (ae_restrict_of_ae (ae_no_coordinate_zero d μ hA))

end DukePrimeDegree

end

end OAI
