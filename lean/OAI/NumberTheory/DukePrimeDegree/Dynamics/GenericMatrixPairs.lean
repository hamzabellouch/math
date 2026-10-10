import OAI.NumberTheory.DukePrimeDegree.Dynamics.LocalOrbitIsolation
import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientNeighborhoods

namespace OAI

/-!
# Small matrix lifts of generic pairs outside a subgroup orbit

If all subgroup orbits are null, a positive-mass generic set contains
arbitrarily close pairs from different orbits. Openness of the actual
quotient orbit map lifts these pairs to matrices tending to identity,
all outside the subgroup. This is a concrete input to polynomial
shearing, without a homogeneous-orbit assumption.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rightSubgroupOrbit {n : ℕ} (L : Subgroup (G n)) (x : X n) : Set (X n) :=
  range (fun h : L => rightAction x h.val)

lemma rightSubgroupOrbit_mk {n : ℕ} (L : Subgroup (G n)) (g : G n) :
    rightSubgroupOrbit L (Quotient.mk _ g) = range (latticeOrbitPoint g L) := by
  ext y
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨Quotient.mk _ h, rfl⟩
  · rintro ⟨a, ha⟩
    induction a using Quotient.inductionOn with
    | h h => exact ⟨h, ha⟩

/-- An actual sequence of small matrices transports one good point to
other good points and never belongs to the given subgroup. -/
theorem exists_small_matrix_generic_pairs {n : ℕ}
    (L : Subgroup (G n)) (μ : Measure (X n)) (E : Set (X n)) (hE : μ E ≠ 0)
    (hnull : ∀ g : G n, μ (range (latticeOrbitPoint g L)) = 0) :
    ∃ x ∈ E, ∃ a : ℕ → G n,
      Tendsto a atTop (𝓝 1) ∧ ∀ k, a k ∉ L ∧ rightAction x (a k) ∈ E := by
  have horbits : ∀ x : X n, μ (rightSubgroupOrbit L x) = 0 := by
    intro x
    induction x using Quotient.inductionOn with
    | h g => rw [rightSubgroupOrbit_mk]; exact hnull g
  obtain ⟨x, hx, hcl⟩ := exists_good_point_in_closure_outside_orbit μ E hE
    (rightSubgroupOrbit L) horbits
  let S : Set (G n) := {g | g ∉ L ∧ rightAction x g ∈ E}
  have hS : (1 : G n) ∈ closure S := by
    apply mem_closure_iff.mpr
    intro U hU h1
    have hUx : x ∈ (fun g => rightAction x g) '' U :=
      ⟨1, h1, rightAction_one x⟩
    obtain ⟨y, ⟨hyU, hyE, hyO⟩⟩ := mem_closure_iff.mp hcl
      ((fun g => rightAction x g) '' U) (rightOrbitMap_isOpen x U hU) hUx
    obtain ⟨g, hgU, rfl⟩ := hyU
    refine ⟨g, hgU, ?_, hyE⟩
    intro hgL
    exact hyO ⟨⟨g, hgL⟩, rfl⟩
  obtain ⟨a, ha, hlim⟩ := mem_closure_iff_seq_limit.mp hS
  exact ⟨x, hx, a, hlim, ha⟩

end DukePrimeDegree

end

end OAI
