import OAI.Analysis.CircleDomains.Topology.SinglePhysicalDisk
import OAI.Analysis.CircleDomains.Topology.SphereNeighborhoods
import OAI.Analysis.CircleDomains.Topology.SphereLevels
import OAI.Analysis.CircleDomains.Topology.TerminalDisks

namespace OAI

/-!
# Physical terminal disks and their staircase oscillations

A finite set of quotient dust points is surrounded by disjoint smooth
physical Jordan disks, with whole fibers inside the disks and boundaries
in the physical domain. The disks can be confined to prescribed
neighborhoods. Liminf and limsup bounds on those neighborhoods give the
staircase oscillation bound `a + 4h`, uniformly in width and shift.
-/

open Set Filter Function Metric
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity.FiniteTransfer

/-- Actual terminal disks, including their smooth boundary parametrizations.
The specified neighborhoods are in the quotient sphere. -/
structure PhysicalTerminalDisks {I : Type*} (G : Set Sphere) (π : Sphere → Sphere)
    (B : Set Sphere) (p : I → Sphere) (O : I → Set Sphere) where
  H : I → ℂ ≃ₜ ℂ
  curve : I → Circle → ℂ
  fiber_subset : ∀ i, {z : ℂ | π (z : Sphere) = p i} ⊆ jordanInterior (H i)
  closure_subset : ∀ i, closure (jordanInterior (H i)) ⊆
    (fun z : ℂ => π (z : Sphere)) ⁻¹' O i
  disjoint_closures : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))
  curve_smooth : ∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (curve i)
  curve_embedding : ∀ i, Topology.IsEmbedding (curve i)
  frontier_eq : ∀ i, frontier (jordanInterior (H i)) = range (curve i)
  frontier_good : ∀ i z, z ∈ frontier (jordanInterior (H i)) →
    (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B

/-- Contours chosen in disjoint connected-complement containers have
disjoint physical closures. Total disconnectedness supplies the singleton
component hypothesis of the single-disk construction. -/
theorem exists_physical_terminal_disks_in_disjoint_containers
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : Type*} (G : Set Sphere) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (p : I → Sphere) (hpB : ∀ i, p i ∈ B) (V : I → Set Sphere)
    (hV : ∀ i, IsOpen (V i)) (hpV : ∀ i, p i ∈ V i)
    (hVconn : ∀ i, IsConnected (V i)ᶜ)
    (hinfty : ∀ i, π OnePoint.infty ∉ closure (V i))
    (hdisj : Pairwise (Disjoint on V)) :
    Nonempty (PhysicalTerminalDisks G π B p V) := by
  classical
  have hcomponent (i : I) : connectedComponentIn B (p i) = {p i} :=
    (hTD _ (connectedComponentIn_subset B (p i))
      isPreconnected_connectedComponentIn).eq_singleton_of_mem
        (mem_connectedComponentIn (hpB i))
  have hsingle (i : I) := exists_single_small_physical_disk
    hsard hschoenflies G π hπ hclosed hsurj hr hB (hpB i)
      (hcomponent i) (hV i) (hpV i) (hVconn i) (hinfty i) hbad
  choose H γ hH using hsingle
  refine ⟨⟨H, γ, fun i => (hH i).1, fun i => (hH i).2.1, ?_,
    fun i => (hH i).2.2.1, fun i => (hH i).2.2.2.1,
    fun i => (hH i).2.2.2.2.1, fun i => (hH i).2.2.2.2.2⟩⟩
  intro i j hij
  exact ((hdisj hij).preimage (fun z : ℂ => π (z : Sphere))).mono
    (hH i).2.1 (hH j).2.1

/-- Finite prescribed neighborhoods can be replaced by disjoint smaller
connected-complement containers. The exclusion of the infinity fiber is
necessary for bounded physical terminal disks. -/
theorem exists_disjoint_physical_terminal_disks
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : Type*} [Fintype I] (G : Set Sphere) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (p : I → Sphere) (hp : Injective p) (hpB : ∀ i, p i ∈ B)
    (hinfty : ∀ i, p i ≠ π OnePoint.infty)
    (O : I → Set Sphere) (hO : ∀ i, O i ∈ 𝓝 (p i)) :
    Nonempty (PhysicalTerminalDisks G π B p O) := by
  classical
  have hdisj : Pairwise (Disjoint on fun i => ({p i} : Set Sphere)) := by
    intro i j hij
    exact disjoint_singleton.mpr (fun h => hij (hp h))
  have hn : Pairwise (Disjoint on fun i => 𝓝ˢ ({p i} : Set Sphere)) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet isClosed_singleton isClosed_singleton (hdisj hij)
  obtain ⟨W, hW, hWd⟩ := hn.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet ({p i} : Set Sphere))
  have hsmall (i : I) : ∃ V : Set Sphere, IsOpen V ∧ p i ∈ V ∧
      closure V ⊆ W i ∩ interior (O i) ∩ ({π OnePoint.infty} : Set Sphere)ᶜ ∧
      IsConnected Vᶜ := by
    apply exists_sphere_neighborhood_connected_compl
      (((hW i).1.inter isOpen_interior).inter isClosed_singleton.isOpen_compl)
    exact ⟨⟨(hW i).2 (mem_singleton _), mem_interior_iff_mem_nhds.mpr (hO i)⟩,
      by simpa using hinfty i⟩
  choose V hV hpV hsub hconn using hsmall
  have hVd : Pairwise (Disjoint on V) := by
    intro i j hij
    exact (hWd hij).mono (fun _ hx => (hsub i (subset_closure hx)).1.1)
      (fun _ hx => (hsub j (subset_closure hx)).1.1)
  obtain ⟨D⟩ := exists_physical_terminal_disks_in_disjoint_containers
    hsard hschoenflies G π hπ hclosed hsurj hr hB hTD hbad p hpB
      V hV hpV hconn (fun i hi => (hsub i hi).2 (mem_singleton _)) hVd
  refine ⟨{ D with closure_subset := ?_ }⟩
  intro i z hz
  change π (z : Sphere) ∈ O i
  exact (interior_subset : interior (O i) ⊆ O i)
    (hsub i (subset_closure (D.closure_subset i hz))).1.2

attribute [local instance] sphereMetric

/-- Actual smooth terminal boundaries obey the enlarged-band staircase
estimate, for all active coordinates simultaneously and for every width
and shift. `hphysical` records that physical points in the prescribed
neighborhood are in the chosen real-branch domain. The neighborhoods may
therefore also impose all desired singularity exclusions. -/
theorem exists_physical_terminals_with_uniform_staircase_oscillation
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I J : Type*} [Fintype I] [Fintype J]
    (G : Set Sphere) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (p : I → Sphere) (hp : Injective p) (hpB : ∀ i, p i ∈ B)
    (hinfty : ∀ i, p i ≠ π OnePoint.infty)
    (O : I → Set Sphere) (hO : ∀ i, O i ∈ 𝓝 (p i))
    (U : I → Set Sphere) (f : I → J → Sphere → ℝ) (M : I → J → ℝ)
    (hM : ∀ i j y, y ∈ U i → |f i j y| ≤ M i j)
    (hphysical : ∀ (i : I) (z : ℂ), (z : Sphere) ∈ G → π (z : Sphere) ∈ O i →
      π (z : Sphere) ∈ U i)
    (active : I → J → Prop) (a : I → J → ℝ)
    (hbudget : ∀ i j, active i j →
      limsup (f i j) (𝓝[U i] (p i)) - liminf (f i j) (𝓝[U i] (p i)) ≤ a i j)
    {h : ℝ} (hh : 0 < h) :
    ∃ D : PhysicalTerminalDisks G π B p O,
      ∀ i j, active i j → ∀ δ θ : ℝ,
        ∀ x ∈ frontier (jordanInterior (D.H i)),
        ∀ y ∈ frontier (jordanInterior (D.H i)),
          |shiftedStaircase h δ θ (f i j (π (x : Sphere))) -
            shiftedStaircase h δ θ (f i j (π (y : Sphere)))| ≤ a i j + 4 * h := by
  classical
  obtain ⟨r, hrpos, hrO, _, hosc⟩ :=
    exists_terminal_balls_with_uniform_staircase_oscillation p hp O hO
      (fun _ => 1) (fun _ => zero_lt_one) U f M hM active a hbudget hh
  obtain ⟨D⟩ := exists_disjoint_physical_terminal_disks hsard hschoenflies
    G π hπ hclosed hsurj hr hB hTD hbad p hp hpB hinfty
      (fun i => ball (p i) (r i)) (fun i => ball_mem_nhds (p i) (hrpos i).1)
  let D' : PhysicalTerminalDisks G π B p O :=
    { D with closure_subset := fun i z hz => hrO i (ball_subset_closedBall
      (D.closure_subset i hz)) }
  refine ⟨D', ?_⟩
  intro i j hj δ θ x hx y hy
  have hxball : π (x : Sphere) ∈ closedBall (p i) (r i) :=
    ball_subset_closedBall (D.closure_subset i (frontier_subset_closure hx))
  have hyball : π (y : Sphere) ∈ closedBall (p i) (r i) :=
    ball_subset_closedBall (D.closure_subset i (frontier_subset_closure hy))
  exact hosc i j hj δ θ (π (x : Sphere))
    ⟨hxball, hphysical i x (D.frontier_good i x hx).1 (hrO i hxball)⟩
    (π (y : Sphere))
    ⟨hyball, hphysical i y (D.frontier_good i y hy).1 (hrO i hyball)⟩

end CircleDomainRigidity.FiniteTransfer

end OAI
