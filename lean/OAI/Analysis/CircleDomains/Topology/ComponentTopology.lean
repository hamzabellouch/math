import OAI.Analysis.CircleDomains.Topology.ComponentControl
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Bases

namespace OAI

/-!
# Topological parts of the component argument

The quotient theorem below proves the totally disconnected dust conclusion
from the component-collapse properties of the quotient.  Moore's 1925
sphere-decomposition theorem supplies the sphere realization; that published
input is not assumed to provide the dust conclusion for free.
-/

open Set Topology

namespace CircleDomainRigidity

theorem IsComplementaryComponent.disjoint_of_ne {G K L : Set Sphere}
    (hK : IsComplementaryComponent G K) (hL : IsComplementaryComponent G L)
    (hne : K ≠ L) : Disjoint K L := by
  obtain ⟨p, _, rfl⟩ := hK
  obtain ⟨q, _, rfl⟩ := hL
  apply Set.disjoint_left.mpr
  intro x hpx hqx
  exact hne ((connectedComponentIn_eq hpx).trans (connectedComponentIn_eq hqx).symm)

/-- No countability is imposed on point components.  The components with
nonempty interior are countable by separability. -/
theorem countable_complementaryComponents_with_interior (G : Set Sphere) :
    {K : Set Sphere | IsComplementaryComponent G K ∧ (interior K).Nonempty}.Countable := by
  let : TopologicalSpace.SeparableSpace Sphere :=
    (OnePoint.isDenseEmbedding_coe (X := ℂ)).separableSpace
  let A := {K : Set Sphere | IsComplementaryComponent G K ∧ (interior K).Nonempty}
  have hdisj : A.PairwiseDisjoint id := by
    intro K hK L hL hne
    exact hK.1.disjoint_of_ne hL.1 hne
  exact hdisj.countable_of_nonempty_interior (fun _ hK => hK.2)

/-- The component quotient of a closed complement has totally disconnected
omitted set.  The hypotheses precisely express the topological quotient,
saturation of the domain, connected fibers, and collapse of each complementary
component; they contain no uniformization or circle-domain conclusion. -/
theorem totallyDisconnected_quotient_complement
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (G : Set X) (hG : IsOpen G) (π : X → Y) (hπ : IsQuotientMap π)
    (hsat : π ⁻¹' (π '' G) = G)
    (hfiber : ∀ y, IsConnected (π ⁻¹' {y}))
    (hcomponent : ∀ x ∈ Gᶜ, π ⁻¹' {π x} = connectedComponentIn Gᶜ x) :
    IsTotallyDisconnected (π '' G)ᶜ := by
  have hopen : IsOpen (π '' G) := hπ.isOpen_preimage.mp (by simpa only [hsat] using hG)
  intro A hAB hA y hy z hz
  have hcl : closure A ⊆ (π '' G)ᶜ :=
    hopen.isClosed_compl.closure_subset_iff.mpr hAB
  have hconn : IsConnected (closure A) := (show IsConnected A from ⟨⟨y, hy⟩, hA⟩).closure
  have hpre : IsConnected (π ⁻¹' closure A) :=
    IsCoinducing.isConnected_preimage_of_isClosed hfiber hπ.isCoinducing
      isClosed_closure hconn
  obtain ⟨p, hp⟩ := hπ.surjective y
  obtain ⟨q, hq⟩ := hπ.surjective z
  have hpA : p ∈ π ⁻¹' closure A := by simpa [hp] using subset_closure hy
  have hqA : q ∈ π ⁻¹' closure A := by simpa [hq] using subset_closure hz
  have hpreG : π ⁻¹' closure A ⊆ Gᶜ := by
    intro x hx hxG
    exact hcl hx ⟨x, hxG, rfl⟩
  have hpG : p ∈ Gᶜ := hpreG hpA
  have hsubset := hpre.isPreconnected.subset_connectedComponentIn hpA hpreG
  have hsame : q ∈ π ⁻¹' {π p} := by
    rw [hcomponent p hpG]
    exact hsubset hqA
  simpa only [mem_preimage, mem_singleton_iff, hp, hq] using hsame.symm

/-- A direct form for the decomposition used in both manuscripts: points of
the domain remain singletons and precisely the complementary components are
collapsed.  Closedness and continuity are the topological quotient input. -/
theorem totallyDisconnected_of_component_collapse
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (G : Set X) (hG : IsOpen G) (π : X → Y) (hcont : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Function.Surjective π)
    (hrel : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    IsTotallyDisconnected (π '' G)ᶜ := by
  have hcomponent (x : X) (hx : x ∈ Gᶜ) :
      π ⁻¹' {π x} = connectedComponentIn Gᶜ x := by
    ext y
    constructor
    · intro hy
      have hxy : π x = π y := (show π y = π x from hy).symm
      rcases (hrel x y).mp hxy with heq | ⟨_, hmem⟩
      · simpa only [← heq] using mem_connectedComponentIn hx
      · exact hmem
    · intro hy
      exact ((hrel x y).mpr (Or.inr ⟨hx, hy⟩)).symm
  have hsingleton (x : X) (hx : x ∈ G) : π ⁻¹' {π x} = {x} := by
    ext y
    constructor
    · intro hy
      rcases (hrel x y).mp (show π x = π y from hy.symm) with hxy | ⟨hx', _⟩
      · exact hxy.symm
      · exact (hx' hx).elim
    · rintro rfl
      rfl
  have hsat : π ⁻¹' (π '' G) = G := by
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      have hxy : x ∈ π ⁻¹' {π y} := heq.symm
      rw [hsingleton y hy] at hxy
      exact hxy ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hfiber (y : Y) : IsConnected (π ⁻¹' {y}) := by
    obtain ⟨x, rfl⟩ := hsurj y
    by_cases hx : x ∈ G
    · rw [hsingleton x hx]
      exact isConnected_singleton
    · rw [hcomponent x hx]
      exact isConnected_connectedComponentIn_iff.mpr hx
  exact totallyDisconnected_quotient_complement G hG π
    (hclosed.isQuotientMap hcont hsurj) hsat hfiber hcomponent

end CircleDomainRigidity

end OAI
