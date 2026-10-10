import OAI.Analysis.CircleDomains.Topology.MooreReduction

namespace OAI

/-!
# Geometry of the component quotient

The quotient is a homeomorphism on the original open domain and has
connected inverse images of continua. Together with `MooreReduction`,
this proves the topological quotient lemma of the Koebe manuscript,
conditional on the precisely stated published Moore input.
-/

open Set Topology

namespace CircleDomainRigidity

/-- A component-collapse quotient restricts to a homeomorphism on the domain. -/
theorem homeomorph_of_component_collapse
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (G : Set X) (hG : IsOpen G) (π : X → Y) (hc : Continuous π)
    (hcl : IsClosedMap π) (hs : Function.Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    IsOpen (π '' G) ∧ ∃ e : G ≃ₜ (π '' G), ∀ x, (e x).val = π x.val := by
  have hsat : π ⁻¹' (π '' G) = G := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      rcases (hr y x).mp hxy with rfl | ⟨hy', _⟩
      · exact hy
      · exact (hy' hy).elim
    · exact fun hx => ⟨x, hx, rfl⟩
  have hq : IsQuotientMap π := hcl.isQuotientMap hc hs
  have hopen : IsOpen (π '' G) := hq.isOpen_preimage.mp (by simpa [hsat] using hG)
  let f := (π '' G).restrictPreimage π
  have hfq : IsQuotientMap f := hq.restrictPreimage_isOpen hopen
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hx : x.val ∈ G := hsat.subset x.property
    rcases (hr x.val y.val).mp (congrArg Subtype.val hxy) with h | ⟨hx', _⟩
    · exact h
    · exact (hx' hx).elim
  let e := Equiv.ofBijective f ⟨hinj, hfq.surjective⟩
  let eh : (π ⁻¹' (π '' G)) ≃ₜ (π '' G) :=
    e.toHomeomorphOfContinuousOpen hfq.continuous
      (hfq.isCoinducing.isOpenMap_of_injective hinj)
  exact ⟨hopen, (Homeomorph.setCongr hsat.symm).trans eh, fun _ => rfl⟩

/-- All fibers of a component-collapse quotient are connected. -/
theorem connected_fibers_of_component_collapse
    {X Y : Type*} [TopologicalSpace X] (G : Set X) (π : X → Y)
    (hs : Function.Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    ∀ y, IsConnected (π ⁻¹' {y}) := by
  intro y
  obtain ⟨x, rfl⟩ := hs y
  by_cases hx : x ∈ G
  · have heq : π ⁻¹' {π x} = {x} := by
      ext z
      constructor
      · intro hz
        rcases (hr x z).mp (show π x = π z from hz.symm) with heq | ⟨hx', _⟩
        · exact heq.symm
        · exact (hx' hx).elim
      · rintro rfl
        rfl
    rw [heq]
    exact isConnected_singleton
  · have heq : π ⁻¹' {π x} = connectedComponentIn Gᶜ x := by
      ext z
      constructor
      · intro hz
        rcases (hr x z).mp (show π x = π z from hz.symm) with heq | ⟨_, hz'⟩
        · exact heq ▸ mem_connectedComponentIn hx
        · exact hz'
      · intro hz
        exact ((hr x z).mpr (Or.inr ⟨hx, hz⟩)).symm
    rw [heq]
    exact isConnected_connectedComponentIn_iff.mpr hx

/-- The complete quotient lemma: only the sphere realization is supplied
by Moore's published theorem; all other conclusions are derived here. -/
theorem quotientSphere_of_moore (hMoore : MooreSphereDecomposition)
    {G : Set Sphere} (hopen : IsOpen G) (hconn : IsConnected G) :
    ∃ π : Sphere → Sphere, Continuous π ∧ IsClosedMap π ∧ Function.Surjective π ∧
      (∀ x y, π x = π y ↔
        x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) ∧
      IsOpen (π '' G) ∧ (∃ e : G ≃ₜ (π '' G), ∀ x, (e x).val = π x.val) ∧
      IsCompact (π '' G)ᶜ ∧ IsTotallyDisconnected (π '' G)ᶜ ∧
      (∀ K : Set Sphere, IsClosed K → IsConnected K → IsConnected (π ⁻¹' K)) := by
  obtain ⟨π, hc, hcl, hs, hr, hdust⟩ := componentSphereQuotient_of_moore hMoore hopen hconn
  obtain ⟨himage, he⟩ := homeomorph_of_component_collapse G hopen π hc hcl hs hr
  refine ⟨π, hc, hcl, hs, hr, himage, he, himage.isClosed_compl.isCompact, hdust, ?_⟩
  intro K hK hKconn
  exact IsCoinducing.isConnected_preimage_of_isClosed
    (connected_fibers_of_component_collapse G π hs hr)
    (hcl.isQuotientMap hc hs).isCoinducing hK hKconn

end CircleDomainRigidity

end OAI
