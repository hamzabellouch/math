import OAI.Analysis.CircleDomains.Topology.GraphFillingDisks
import OAI.Analysis.CircleDomains.Transfer.GridCoordinateFilling
import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanPhysicalBranches

namespace OAI

/-! The graph avoidance supplied by the subordinate contour construction
implies exactly the inactive lattice avoidance of its local real lifts.
This applies equally to real coordinates and genuine period coordinates. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem graph_branch_avoids_lattice_on_real_boundary
    (R : Set (Sphere × UnitAddCircle)) (q : ℂ → Sphere) (H : ℂ ≃ₜ ℂ)
    (u : (ℝ × ℝ) → ℝ)
    (hgraph : ∀ z ∈ frontier (jordanInterior H),
      (q z, (u (Complex.equivRealProdCLM z) : UnitAddCircle)) ∈ R)
    {N : ℕ} {θ : ℝ}
    (havoid : Disjoint (frontier (jordanInterior H))
      (q ⁻¹' (⋃ j, reciprocalGraphLevel R θ N j))) :
    Disjoint (u '' frontier (realJordanInterior H)) (shiftedLattice (reciprocalGridStep N) θ) := by
  apply Set.disjoint_left.mpr
  rintro r ⟨x, hx, rfl⟩ hr
  rw [frontier_realJordanInterior] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨j, hj⟩ := exists_reciprocal_level_of_mem_lattice hr
  apply Set.disjoint_left.mp havoid hz
  refine mem_iUnion.mpr ⟨j, ?_⟩
  change (q z, ((θ + (j.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle)) ∈ R
  rw [← hj]
  exact hgraph z hz

 theorem exists_masked_graph_boundary_active
    {I : Type*} {n N : ℕ} (hn : 0 < n)
    (R : Fin n → Set (Sphere × UnitAddCircle)) (q : ℂ → Sphere)
    (H : I → ℂ ≃ₜ ℂ) (u : I → Fin n → (ℝ × ℝ) → ℝ)
    (present : I → Fin n → Prop)
    (hgraph : ∀ i l, present i l → ∀ z ∈ frontier (jordanInterior (H i)),
      (q z, (u i l (Complex.equivRealProdCLM z) : UnitAddCircle)) ∈ R l)
    (θ : Fin n → ℝ)
    (hgrid : ∀ i, ∃ k : ℕ, ∀ l : Fin n, l.val ≠ k →
      Disjoint (frontier (jordanInterior (H i)))
        (q ⁻¹' (⋃ j, reciprocalGraphLevel (R l) (θ l) N j))) :
    ∃ active : I → Fin n, ∀ i l, present i l → l ≠ active i →
      Disjoint (u i l '' frontier (realJordanInterior (H i)))
        (shiftedLattice (reciprocalGridStep N) (θ l)) := by
  have hex (i : I) : ∃ a : Fin n, ∀ l, l ≠ a →
      (present i l → Disjoint (u i l '' frontier (realJordanInterior (H i)))
        (shiftedLattice (reciprocalGridStep N) (θ l))) := by
    apply exists_active_coordinate_of_single_exception hn
    obtain ⟨k, hk⟩ := hgrid i
    refine ⟨k, fun l hl hp => ?_⟩
    exact graph_branch_avoids_lattice_on_real_boundary (R l) q (H i) (u i l)
      (hgraph i l hp) (hk l hl)
  choose a ha using hex
  exact ⟨a, fun i l hp hl => ha i l hl hp⟩

end CircleDomainRigidity.FiniteTransfer

namespace CircleDomainRigidity
open FiniteTransfer

 theorem SmoothMeanPeriodData.physical_mem_graph
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : MeasureTheory.ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} {b : Sphere} {π : Sphere → Sphere}
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    {z : ℂ} (hzG : (z : Sphere) ∈ G) (hzU : π (z : Sphere) ∈ U)
    (hzM : π (z : Sphere) ∈ M) (hzS : π (z : Sphere) ∈ S) :
    (π (z : Sphere), Q.physical z) ∈ periodBandGraph U M b Q.patch Q.branch := by
  exact (Q.domain_value _ hzU _).mpr ⟨hzM, (Q.physical_value z hzG hzS).symm⟩

end CircleDomainRigidity

end

end OAI
