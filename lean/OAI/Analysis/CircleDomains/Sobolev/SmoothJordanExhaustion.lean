import OAI.Analysis.CircleDomains.Topology.PrescribedJordanCore
import OAI.Analysis.CircleDomains.Topology.ConnectedCoreNeighborhood

namespace OAI

/-!
# A strict exhaustion by finite smooth Jordan cores

Every prescribed compact subset is retained in the interior of a finite
Jordan core. Recursive application retains the preceding core and the next
compact exhaustion set. The construction uses Sard, one-manifold
classification, and Schoenflies.
-/

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

structure SmoothJordanCore (G : Set Sphere) where
  count : ℕ
  disk : Fin count → ℂ ≃ₜ ℂ
  curve : Fin count → Circle → ℂ
  disjoint : Pairwise (Disjoint on fun i => closure (jordanInterior (disk i)))
  subset_domain : closedJordanCore disk ⊆ G
  smooth : ∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (curve i)
  embedding : ∀ i, Topology.IsEmbedding (curve i)
  boundary : ∀ i, frontier (jordanInterior (disk i)) = range (curve i)

namespace SmoothJordanCore

variable {G : Set Sphere} (C : SmoothJordanCore G)

def carrier : Set Sphere := closedJordanCore C.disk

theorem isCompact : IsCompact C.carrier :=
  (isOpen_iUnion fun i => OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (C.disk i))).isClosed_compl.isCompact

theorem subset : C.carrier ⊆ G := C.subset_domain

theorem regular : closure (interior C.carrier) = C.carrier :=
  closure_interior_closedJordanCore C.disk C.disjoint

theorem connected_interior : IsConnected (interior C.carrier) := by
  rw [carrier, interior_closedJordanCore]
  exact isConnected_openCompletedRegion C.disk C.disjoint

theorem infty_interior : OnePoint.infty ∈ interior C.carrier := by
  rw [carrier, interior_closedJordanCore]
  intro h
  obtain ⟨i, z, _, hz⟩ := mem_iUnion.mp h
  exact OnePoint.coe_ne_infty z hz

end SmoothJordanCore

theorem exists_smooth_jordan_core_containing
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G S : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hS : IsCompact S) (hSG : S ⊆ G) :
    ∃ C : SmoothJordanCore G, S ⊆ interior C.carrier := by
  obtain ⟨P, hPc, hPconn, hPG, hSP, hinfP⟩ :=
    exists_compact_connected_core_neighborhood hG hconn hinf hS hSG
  obtain ⟨n, H, γ, hd, hKG, hPK, hcurves⟩ :=
    exists_prescribed_jordan_core hsard hschoenflies hG hPc hPG hPconn.isPreconnected hinfP
  let C : SmoothJordanCore G := ⟨n, H, γ, hd, hKG,
    fun i => (hcurves i).1, fun i => (hcurves i).2.1, fun i => (hcurves i).2.2⟩
  exact ⟨C, (hSP.trans interior_subset).trans hPK⟩

theorem exists_smooth_jordan_exhaustion
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) :
    ∃ C : ℕ → SmoothJordanCore G,
      (∀ n, (C n).carrier ⊆ interior (C (n + 1)).carrier) ∧
      (⋃ n, interior (C n).carrier) = G := by
  classical
  obtain ⟨R, D, K, _, _, _, _, _, hK, hDK, hcover, _, _⟩ :=
    exists_sphere_connected_core_exhaustion hG hconn hinf
  have hex (S : Set Sphere) (hS : IsCompact S) (hSG : S ⊆ G) :=
    exists_smooth_jordan_core_containing hsard hschoenflies hG hconn hinf hS hSG
  let initial : SmoothJordanCore G := Classical.choose (hex (K 0) (hK 0).1 (hK 0).2)
  have hinitial : K 0 ⊆ interior initial.carrier :=
    Classical.choose_spec (hex (K 0) (hK 0).1 (hK 0).2)
  let next (n : ℕ) (C : SmoothJordanCore G) : SmoothJordanCore G :=
    Classical.choose (hex (C.carrier ∪ K (n + 1))
      (C.isCompact.union (hK (n + 1)).1) (union_subset C.subset (hK (n + 1)).2))
  have hnext (n : ℕ) (C : SmoothJordanCore G) :
      C.carrier ∪ K (n + 1) ⊆ interior (next n C).carrier :=
    Classical.choose_spec (hex (C.carrier ∪ K (n + 1))
      (C.isCompact.union (hK (n + 1)).1) (union_subset C.subset (hK (n + 1)).2))
  let C : ℕ → SmoothJordanCore G := fun n => Nat.rec initial next n
  have hstep (n : ℕ) : C (n + 1) = next n (C n) := rfl
  have hretain (n : ℕ) : K n ⊆ interior (C n).carrier := by
    cases n with
    | zero => exact hinitial
    | succ n => exact subset_union_right.trans (hnext n (C n))
  refine ⟨C, fun n => subset_union_left.trans (hnext n (C n)), ?_⟩
  apply Subset.antisymm
  · exact iUnion_subset fun n => interior_subset.trans (C n).subset
  · intro p hp
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hp)
    exact mem_iUnion.mpr ⟨n, hretain n (interior_subset (hDK n hn))⟩

end CircleDomainRigidity

end

end OAI
