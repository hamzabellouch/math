import OAI.Combinatorics.Crossing.FiniteDiskCollar
import OAI.Combinatorics.Crossing.PathEndpointNeighborhoods
import OAI.Combinatorics.Crossing.PolygonalBoundaryReplacement

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem exterior_arc_polygonal_replacement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → Plane) (r : ℝ) (hr : 0 < r)
    (hd : ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r))
    (k l : ι) (a b : Plane) (hab : a ≠ b)
    (ha : squaredLength (a-z k)=r^2) (hb : squaredLength (b-z l)=r^2)
    (γ : Path a b) (U : Set Plane) (hU : IsOpen U) (hγU : ∀ t, γ t ∈ U)
    (hγout : ∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → γ t ∈ outsideDisks z r) :
    ∃ P : PolygonalChain U a b, Function.Injective P.path ∧
      (∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → P.path t ∈ outsideDisks z r) := by
  obtain ⟨α,ρ,hα,hρ,hspurA,hnearA⟩ := exists_finite_disk_collar z r hr hd k a ha U hU
    (by simpa using hγU 0)
  obtain ⟨β,σ,hβ,hσ,hspurB,hnearB⟩ := exists_finite_disk_collar z r hr hd l b hb U hU
    (by simpa using hγU 1)
  obtain ⟨u,v,hu0,huv,hv1,hu,hv⟩ := path_near_endpoints γ ρ σ hρ hσ
  let a' := a+α • (a-z k)
  let b' := b+β • (b-z l)
  let O := U ∩ outsideDisks z r
  have hO : IsOpen O := hU.inter (isOpen_outsideDisks z r)
  have hleft : segment ℝ a' (γ u) ⊆ O := hnearA (γ u) hu (hγout u ⟨hu0,huv.trans hv1⟩)
  have hright : segment ℝ (γ v) b' ⊆ O := by
    rw [segment_symm]
    exact hnearB (γ v) hv (hγout v ⟨hu0.trans huv,hv1⟩)
  have hmiddle : Set.range (pathSubarc γ u v) ⊆ O := by
    rw [pathSubarc_range γ u v huv]
    rintro x ⟨t,ht,rfl⟩
    exact ⟨hγU t,hγout t ⟨hu0.trans_le ht.1,ht.2.trans_lt hv1⟩⟩
  let η : Path a' b' := (Path.segment a' (γ u)).trans
    ((pathSubarc γ u v).trans (Path.segment (γ v) b'))
  have hη : Set.range η ⊆ O := by
    dsimp [η]
    rw [Path.trans_range,Path.trans_range,Path.range_segment,Path.range_segment]
    exact Set.union_subset hleft (Set.union_subset hmiddle hright)
  have hA : segment ℝ a a' ⊆ insert a (insert b O) := by
    intro x hx
    obtain ⟨hxU,hxa | hxout⟩ := hspurA hx
    · exact Or.inl hxa
    · exact Or.inr (Or.inr ⟨hxU,hxout⟩)
  have hB : segment ℝ b' b ⊆ insert a (insert b O) := by
    rw [segment_symm]
    intro x hx
    obtain ⟨hxU,hxb | hxout⟩ := hspurB hx
    · exact Or.inr (Or.inl hxb)
    · exact Or.inr (Or.inr ⟨hxU,hxout⟩)
  obtain ⟨Q,hQ,hQout⟩ := polygonal_replacement_with_spurs O hO a a' b' b hab η
    (fun t => hη ⟨t,rfl⟩) hA hB
  have hSU : insert a (insert b O) ⊆ U := by
    intro x hx
    rcases hx with rfl | rfl | hx
    · simpa using hγU 0
    · simpa using hγU 1
    · exact hx.1
  exact ⟨Q.widen hSU,hQ,fun t ht => (hQout t ht).2⟩

end Zarankiewicz

end

end OAI
