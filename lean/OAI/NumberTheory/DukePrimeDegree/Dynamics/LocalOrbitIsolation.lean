import OAI.NumberTheory.DukePrimeDegree.Dynamics.PositiveOrbitRestriction
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Sequences

namespace OAI

/-!
# Local orbit isolation gives a positive-mass orbit

The topological conclusion needed from the shearing argument is local
isolation of the invariant-group orbits inside one positive-mass good
set. Second countability then produces a countable orbit cover, so one
actual orbit has positive mass. No finite-orbit existence is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

/-- A positive-mass set locally covered by single members of a family
has positive mass in one family member. The family members need not be
open, measurable, or countable. -/
theorem exists_positive_member_of_local_cover
    {Y I : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
    (μ : Measure Y) (E : Set Y) (hE : μ E ≠ 0) (O : I → Set Y)
    (hlocal : ∀ x ∈ E, ∃ (i : I) (U : Set Y),
      IsOpen U ∧ x ∈ U ∧ E ∩ U ⊆ O i) :
    ∃ i : I, μ (O i) ≠ 0 := by
  classical
  choose i U hUopen hUx hUsub using fun x : E => hlocal x.val x.property
  have hcover : E ⊆ ⋃ x : E, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hUx ⟨x, hx⟩⟩
  obtain ⟨J, hJcount, hJcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof E).elim_countable_subcover U hUopen hcover
  by_contra hnone
  push Not at hnone
  have hzero : μ (⋃ x ∈ J, E ∩ U x) = 0 :=
    (measure_biUnion_null_iff hJcount).mpr fun x _ =>
      measure_mono_null (hUsub x) (hnone (i x))
  apply hE
  apply measure_mono_null _ hzero
  intro x hx
  obtain ⟨y, hyJ, hyU⟩ := mem_iUnion₂.mp (hJcover hx)
  exact mem_iUnion₂.mpr ⟨y, hyJ, hx, hyU⟩

/-- If every orbit is null, every positive-mass good set contains a
point approached by good points from outside its orbit. -/
theorem exists_good_point_in_closure_outside_orbit
    {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
    (μ : Measure Y) (E : Set Y) (hE : μ E ≠ 0) (O : Y → Set Y)
    (hnull : ∀ x, μ (O x) = 0) :
    ∃ x ∈ E, x ∈ closure (E \ O x) := by
  classical
  by_contra hnone
  push Not at hnone
  have hlocal : ∀ x ∈ E, ∃ (i : Y) (U : Set Y),
      IsOpen U ∧ x ∈ U ∧ E ∩ U ⊆ O i := by
    intro x hx
    refine ⟨x, (closure (E \ O x))ᶜ, isClosed_closure.isOpen_compl, hnone x hx, ?_⟩
    rintro y ⟨hyE, hyU⟩
    by_contra hyO
    exact hyU (subset_closure ⟨hyE, hyO⟩)
  obtain ⟨x, hx⟩ := exists_positive_member_of_local_cover μ E hE O hlocal
  exact hx (hnull x)

theorem exists_good_sequence_outside_orbit
    {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
    (μ : Measure Y) (E : Set Y) (hE : μ E ≠ 0) (O : Y → Set Y)
    (hnull : ∀ x, μ (O x) = 0) :
    ∃ x ∈ E, ∃ y : ℕ → Y, (∀ k, y k ∈ E ∧ y k ∉ O x) ∧
      Tendsto y atTop (𝓝 x) := by
  obtain ⟨x, hx, hcl⟩ := exists_good_point_in_closure_outside_orbit μ E hE O hnull
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.mp hcl
  exact ⟨x, hx, y, hy, hlim⟩

/-- For the actual closed measure stabilizer, local orbit isolation is
enough for the previously proved prime-degree Haar obstruction. The
isolation premise is an intermediate shearing target, not a replacement
for the published rigidity theorem. -/
theorem isHaar_of_local_invariant_orbit_isolation
    (d : ℕ) (hprime : (d + 1).Prime)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (r : Setoid (Fin (d + 1)))
    (hr : ∀ i j, r i j ↔ rootInvarianceRelation μ i j)
    (hnontrivial : ∃ i j, i ≠ j ∧ r i j)
    (E : Set (X (d + 1))) (hE : μ E ≠ 0)
    (hlocal : ∀ x ∈ E, ∃ (g : G (d + 1)) (U : Set (X (d + 1))),
      IsOpen U ∧ x ∈ U ∧ E ∩ U ⊆ range (latticeOrbitPoint g (invariantRightSubgroup μ))) :
    IsHaarProbability μ := by
  obtain ⟨g, hg⟩ := exists_positive_member_of_local_cover μ E hE
    (fun g => range (latticeOrbitPoint g (invariantRightSubgroup μ))) hlocal
  exact isHaar_of_positive_invariantSubgroup_orbit d hprime μ hA r hr hnontrivial g hg

end DukePrimeDegree

end

end OAI
