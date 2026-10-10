import OAI.Analysis.CircleDomains.Sobolev.SmoothJordanExhaustion
import OAI.Analysis.CircleDomains.Topology.ImageCoreJordan
import OAI.Analysis.CircleDomains.Topology.JordanEndComponents

namespace OAI

/-!
# Actual image-core chains for every complementary component

The source cores and their boundary parametrizations are constructed. Their
images determine finite disjoint target Jordan families; every component of
the complement of the conformal image is the strictly nested intersection
of the selected target disks.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_jordan_chain_for_complementary_component
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G)
    {f : Sphere → Sphere} (hf : IsConformalOn f G) (hi : InjOn f G)
    (hfix : f OnePoint.infty = OnePoint.infty)
    {p : Sphere} (hp : p ∈ (f '' G)ᶜ) :
    ∃ (C : ℕ → SmoothJordanCore G)
      (H : (n : ℕ) → Fin (C n).count → ℂ ≃ₜ ℂ) (b : (n : ℕ) → Fin (C n).count),
      (∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier) ∧
      (⋃ n, interior (C n).carrier) = G ∧
      (∀ n i, frontier (jordanInterior (H n i)) =
        range (fun t => finiteCoord (f (((C n).curve i t : ℂ) : Sphere)))) ∧
      (∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (H n i)))) ∧
      connectedComponentIn (f '' G)ᶜ p = ⋂ n, closedTerminalCap (H n (b n)) ∧
      (∀ n, closedTerminalCap (H (n + 1) (b (n + 1))) ⊆
        ((↑) : ℂ → Sphere) '' jordanInterior (H n (b n))) ∧
      ∀ n, connectedComponentIn (f '' G)ᶜ p ⊆
        ((↑) : ℂ → Sphere) '' jordanInterior (H n (b n)) := by
  classical
  obtain ⟨C, hCstrict, hCcover⟩ := exists_smooth_jordan_exhaustion
    hsard hschoenflies hG hconn hinf
  have hdata (n : ℕ) := exists_jordan_image_core hschoenflies hG hf hi
    (C n).isCompact (C n).subset (C n).regular (C n).connected_interior.isPreconnected
    (C n).infty_interior hfix (C n).curve (fun i => ((C n).embedding i).continuous)
    (fun i => ((C n).embedding i).injective) (show Pairwise (fun i j =>
      Disjoint (range ((C n).curve i)) (range ((C n).curve j))) from by
        intro i j hij
        apply ((C n).disjoint hij).mono
        · rw [← (C n).boundary i]
          exact frontier_subset_closure
        · rw [← (C n).boundary j]
          exact frontier_subset_closure)
    (show frontier (C n).carrier = ⋃ i, ((↑) : ℂ → Sphere) '' range ((C n).curve i) from by
      rw [SmoothJordanCore.carrier, frontier_closedJordanCore (C n).disk (C n).disjoint]
      simp only [(C n).boundary])
  choose H hHfront hHd hHe using hdata
  let A : ℕ → Set Sphere := fun n => f '' (C n).carrier
  have hAstrict (n : ℕ) : A n ⊆ interior (A (n + 1)) := by
    change f '' (C n).carrier ⊆ interior (f '' (C (n + 1)).carrier)
    rw [interior_image_compact_core hf hG hi (C (n + 1)).subset]
    exact image_mono (hCstrict n)
  have hAcover : (⋃ n, A n) = f '' G := by
    apply Subset.antisymm
    · exact iUnion_subset fun n => image_mono (C n).subset
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hCcover.symm ▸ hx)
      exact mem_iUnion.mpr ⟨n, x, interior_subset hn, rfl⟩
  obtain ⟨b, hb, hnest, hinside⟩ := component_eq_nested_jordan_end H hHd A hHe hAstrict hAcover hp
  exact ⟨C, H, b, hCstrict, hCcover, hHfront, hHd, hb, hnest, hinside⟩

end CircleDomainRigidity

end

end OAI
