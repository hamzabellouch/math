import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactLifts
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen

namespace OAI

/-! # Multiplication of overlapping Cartan factors

Compatible conjugation gives the actual multiplication homomorphism from the
semidirect product. Its kernel records the overlap. Local surjectivity makes
it globally surjective in a connected ambient group, and an open product map
then has compact lifts of compact sets. No complementary subgroup is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Topology
open scoped Topology

section OpenProduct

variable {N D G : Type*} [Group N] [Group D] [Group G]
  [TopologicalSpace N] [TopologicalSpace D] [TopologicalSpace G]
  [IsTopologicalGroup N] [IsTopologicalGroup D] [IsTopologicalGroup G]

/-- For a product of two homomorphisms, openness at the identity propagates
to every point by independent left and right translations. -/
theorem isOpenMap_factorProduct_of_map_nhds_one
    (ι : N →* G) (κ : D →* G)
    (hlocal : Filter.map (fun p : N × D => ι p.1 * κ p.2) (𝓝 1) = 𝓝 1) :
    IsOpenMap (fun p : N × D => ι p.1 * κ p.2) := by
  let f : N × D → G := fun p => ι p.1 * κ p.2
  apply IsOpenMap.of_nhds_le
  intro p
  let t : N × D ≃ₜ N × D :=
    (Homeomorph.mulLeft p.1).prodCongr (Homeomorph.mulRight p.2)
  let s : G ≃ₜ G := (Homeomorph.mulLeft (ι p.1)).trans (Homeomorph.mulRight (κ p.2))
  have ht : t 1 = p := by
    change (p.1 * 1, 1 * p.2) = p
    simp only [mul_one, one_mul, Prod.eta]
  have hs : s 1 = f p := by simp [s, f]
  have hcomm : f ∘ t = s ∘ f := by
    funext q
    simp [t, s, f, map_mul, mul_assoc]
  have hm : Filter.map f (𝓝 p) = 𝓝 (f p) := by
    rw [← ht, ← t.map_nhds_eq, Filter.map_map, hcomm, ← Filter.map_map,
      hlocal, s.map_nhds_eq, hs]
    rw [ht]
  exact hm.ge

end OpenProduct

variable {N D G : Type*} [Group N] [Group D] [Group G]
  (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
  (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)

/-- Actual factor multiplication as a group homomorphism. -/
def cartanMultiplication : N ⋊[φ] D →* G :=
  SemidirectProduct.lift ι κ (fun d => by
    ext n
    exact hconj d n)

@[simp] theorem cartanMultiplication_apply (z : N ⋊[φ] D) :
    cartanMultiplication ι κ φ hconj z = ι z.left * κ z.right := rfl

/-- This kernel equation retains the entire overlap of the factors. -/
theorem mem_cartanMultiplication_ker (z : N ⋊[φ] D) :
    z ∈ (cartanMultiplication ι κ φ hconj).ker ↔ ι z.left = (κ z.right)⁻¹ := by
  simp only [MonoidHom.mem_ker, cartanMultiplication_apply, mul_eq_one_iff_eq_inv]

/-- The range agrees with the ordinary product parameterization, even when
its fibers are nontrivial. -/
theorem range_cartanMultiplication :
    Set.range (cartanMultiplication ι κ φ hconj) =
      Set.range (fun p : N × D => ι p.1 * κ p.2) := by
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(z.left, z.right), rfl⟩
  · rintro ⟨⟨n, d⟩, rfl⟩
    exact ⟨⟨n, d⟩, rfl⟩

/-- Projection of the kernel to the ambient group is injective when each
factor inclusion is injective. Thus no further kernel is silently discarded. -/
theorem cartan_kernel_projection_injective
    (hι : Function.Injective ι) (hκ : Function.Injective κ) :
    Function.Injective (fun z : (cartanMultiplication ι κ φ hconj).ker => κ z.val.right) := by
  intro z w hzw
  have hd : z.val.right = w.val.right := hκ hzw
  apply Subtype.ext
  apply SemidirectProduct.ext
  · apply hι
    have hz := (mem_cartanMultiplication_ker ι κ φ hconj z.val).mp z.property
    have hw := (mem_cartanMultiplication_ker ι κ φ hconj w.val).mp w.property
    rw [hz, hw, hd]
  · exact hd

/-- The image of that kernel projection is precisely the factor intersection. -/
theorem cartan_kernel_projection_range :
    Set.range (fun z : (cartanMultiplication ι κ φ hconj).ker => κ z.val.right) =
      (ι.range : Set G) ∩ (κ.range : Set G) := by
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨?_, ⟨z.val.right, rfl⟩⟩
    have hz := (mem_cartanMultiplication_ker ι κ φ hconj z.val).mp z.property
    refine ⟨z.val.left⁻¹, ?_⟩
    rw [map_inv, hz, inv_inv]
  · rintro ⟨⟨n, hn⟩, ⟨d, hd⟩⟩
    have hz : (⟨n⁻¹, d⟩ : N ⋊[φ] D) ∈ (cartanMultiplication ι κ φ hconj).ker := by
      rw [mem_cartanMultiplication_ker]
      change ι n⁻¹ = (κ d)⁻¹
      rw [map_inv, hn, hd]
    exact ⟨⟨⟨n⁻¹, d⟩, hz⟩, hd⟩

variable [TopologicalSpace G] [IsTopologicalGroup G] [PreconnectedSpace G]

/-- A local product neighborhood is enough for global factorization in the
connected ambient group. -/
theorem cartanMultiplication_surjective_of_range_mem_nhds
    (hlocal : Set.range (fun p : N × D => ι p.1 * κ p.2) ∈ 𝓝 (1 : G)) :
    Function.Surjective (cartanMultiplication ι κ φ hconj) := by
  let q := cartanMultiplication ι κ φ hconj
  have hn : (q.range : Set G) ∈ 𝓝 (1 : G) := by
    change Set.range q ∈ 𝓝 (1 : G)
    rwa [range_cartanMultiplication]
  have ho := q.range.isOpen_of_mem_nhds hn
  have hc : IsClopen (q.range : Set G) := ⟨q.range.isClosed_of_isOpen ho, ho⟩
  have he := hc.eq_univ ⟨1, q.range.one_mem⟩
  intro g
  have hg : g ∈ (q.range : Set G) := he.symm ▸ mem_univ g
  exact hg

variable [TopologicalSpace N] [TopologicalSpace D] [LocallyCompactSpace (N × D)]

include hconj in
/-- Once the local product map is open, every compact set admits compact
factor lifts. The kernel can be arbitrary. -/
theorem exists_compact_cartan_factor_lifts
    (hlocal : Set.range (fun p : N × D => ι p.1 * κ p.2) ∈ 𝓝 (1 : G))
    (hopen : IsOpenMap (fun p : N × D => ι p.1 * κ p.2))
    {K : Set G} (hK : IsCompact K) :
    ∃ C : Set (N × D), IsCompact C ∧ K ⊆ (fun p : N × D => ι p.1 * κ p.2) '' C := by
  apply exists_compact_lifts_of_open_surjection _ hopen _ hK
  intro g
  obtain ⟨z, hz⟩ := cartanMultiplication_surjective_of_range_mem_nhds ι κ φ hconj hlocal g
  exact ⟨(z.left, z.right), hz⟩

end PolycyclicRecognition

end

end OAI
