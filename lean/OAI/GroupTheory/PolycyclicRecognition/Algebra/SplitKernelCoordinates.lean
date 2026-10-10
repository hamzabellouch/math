import OAI.GroupTheory.PolycyclicRecognition.Algebra.ProductLocalCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConnectedHomCovering
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SimplyConnectedRetraction

namespace OAI

/-! # Identifying an integrated kernel from local product coordinates

A normalized section turns a local product map into a product with the
identity. The actual kernel is simply connected by retraction. A connected
source with these local coordinates therefore maps homeomorphically onto
that kernel, and its inclusion in the ambient group is closed.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Topology
open scoped ContinuousMap

variable {N G Q : Type*}
  [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (π : G →* Q) (hπ : Continuous π) (s : C(Q, G))
  (hs : ∀ q, π (s q) = q) (hsone : s 1 = 1)
  (f : N →* G) (hf : ∀ n, π (f n) = 1)

omit [IsTopologicalGroup Q] in
include hπ hs hsone hf in
theorem localHomeomorph_kernel_of_split_coordinates
    (hinj : ∃ U ∈ 𝓝 ((1 : N), (1 : Q)),
      InjOn (fun p : N × Q => f p.1 * s p.2) U)
    (hmap : map (fun p : N × Q => f p.1 * s p.2) (𝓝 (1, 1)) = 𝓝 (1 : G)) :
    IsLocalHomeomorph (f.codRestrict π.ker hf) := by
  let e := (quotientSectionHomeomorph π hπ s hs).trans (Homeomorph.prodComm Q π.ker)
  let k := f.codRestrict π.ker hf
  have he (p : N × Q) : e (f p.1 * s p.2) = (k p.1, p.2) := by
    apply Prod.ext
    · apply Subtype.ext
      change (f p.1 * s p.2) * (s (π (f p.1 * s p.2)))⁻¹ = f p.1
      rw [map_mul, hf, hs, one_mul]
      exact mul_inv_cancel_right _ _
    · change π (f p.1 * s p.2) = p.2
      rw [map_mul, hf, hs, one_mul]
  have heone : e 1 = (1, 1) := by
    have hh := he (1, 1)
    simpa only [map_one, hsone, mul_one] using hh
  apply localHomeomorph_hom_of_prodMap k (1 : Q)
  · obtain ⟨U, hU, hi⟩ := hinj
    refine ⟨U, hU, ?_⟩
    intro a ha b hb hab
    apply hi ha hb
    apply e.injective
    rw [he, he]
    exact hab
  · have heq : (fun p : N × Q => (k p.1, p.2)) =
        e ∘ (fun p : N × Q => f p.1 * s p.2) := (funext he).symm
    rw [heq, ← map_map, hmap, e.map_nhds_eq, heone]

include hπ hs hsone hf in
theorem closedEmbedding_kernel_of_split_coordinates
    [PreconnectedSpace N] [LocallyPathConnectedSpace N]
    [SimplyConnectedSpace G] [T2Space Q]
    (hinj : ∃ U ∈ 𝓝 ((1 : N), (1 : Q)),
      InjOn (fun p : N × Q => f p.1 * s p.2) U)
    (hmap : map (fun p : N × Q => f p.1 * s p.2) (𝓝 (1, 1)) = 𝓝 (1 : G)) :
    Topology.IsClosedEmbedding f ∧ Set.range f = (π.ker : Set G) := by
  let k := f.codRestrict π.ker hf
  have hlocal : IsLocalHomeomorph k :=
    localHomeomorph_kernel_of_split_coordinates π hπ s hs hsone f hf hinj hmap
  let : SimplyConnectedSpace π.ker :=
    simplyConnectedSpace_kernel_of_section π hπ s hs hsone
  have hkmap : map k (𝓝 1) = 𝓝 1 := by simpa only [map_one] using hlocal.map_nhds_eq 1
  have hsurj := surjective_of_hom_map_nhds_one k hkmap
  let : LocallyPathConnectedSpace π.ker :=
    (hlocal.isOpenMap.isQuotientMap hlocal.continuous hsurj).locallyPathConnectedSpace
  obtain ⟨U, hU, h1, hi⟩ := hlocal.isLocallyInjective 1
  have hbij := bijective_of_hom_local_coordinates k hkmap ⟨U, hU.mem_nhds h1, hi⟩
  let e := hlocal.toHomeomorphOfBijective hbij
  have hclosed : IsClosed (π.ker : Set G) := isClosed_eq hπ continuous_const
  constructor
  · exact hclosed.isClosedEmbedding_subtypeVal.comp e.isClosedEmbedding
  · ext g
    constructor
    · rintro ⟨n, rfl⟩
      exact hf n
    · intro hg
      obtain ⟨n, hn⟩ := hsurj ⟨g, hg⟩
      exact ⟨n, congrArg Subtype.val hn⟩

end PolycyclicRecognition

end

end OAI
