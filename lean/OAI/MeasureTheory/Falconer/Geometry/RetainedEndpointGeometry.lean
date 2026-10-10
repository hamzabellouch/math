import OAI.MeasureTheory.Falconer.Estimates.ChildRetention
import OAI.MeasureTheory.Falconer.Estimates.LocalPrefixCenters

namespace OAI

/-! The geometric profile bounds survive each actual class refinement.
Both endpoint sets use the same original dyadic centers and local similarity. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_retained_endpoint_geometry {N : ℕ}
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).card:ℝ) ≤
      M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i))) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let a := blockDepth N B i
    let b := blockDepth N B j
    let F := localPacketPoint (1/(2:ℝ)^a) ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1)
    let ZC := ((prefixChildren C a b p₀).image (fun r => (Q.descendant r).center)).image F
    let ZS := ((prefixChildren S a b p₀).image (fun r => (Q.descendant r).center)).image F
    ZS.Nonempty ∧ ZS ⊆ ZC ∧ InBoundedLineChart ZS ∧
      FiniteSeparatedAt (1/(2:ℝ)^(b-a)) ZS ∧
      (ZC.card:ℝ) ≤ (M*(2:ℝ)^(2*i+2*j))*(ZS.card:ℝ) ∧
      ∀ s A : ℝ, 0 ≤ A → NormalizedFiniteBallBound (1/(2:ℝ)^(b-a)) s A ZC →
        NormalizedFiniteBallBound (1/(2:ℝ)^(b-a)) s (A*(M*(2:ℝ)^(2*i+2*j))) ZS := by
  let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
  let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
  let a := blockDepth N B i
  let b := blockDepth N B j
  let F := localPacketPoint (1/(2:ℝ)^a) ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1)
  let DC := prefixChildren C a b p₀
  let DS := prefixChildren S a b p₀
  let ZC := (DC.image (fun r => (Q.descendant r).center)).image F
  let ZS := (DS.image (fun r => (Q.descendant r).center)).image F
  have hCN : C ⊆ cubePaths 2 N := (Finset.filter_subset _ _).trans hL
  have hSN : S ⊆ cubePaths 2 N := (Finset.filter_subset _ _).trans hL'
  have hab : a ≤ b := blockDepth_antitone N B hji
  have hbn : b ≤ N := Nat.sub_le _ _
  obtain ⟨hcC,_,_⟩ := local_prefix_centers_geometry Q hQ C hCN hab hbn p₀
  obtain ⟨hcS,hchart,hsep⟩ := local_prefix_centers_geometry Q hQ S hSN hab hbn p₀
  have hDS : DS ⊆ DC := Finset.image_subset_image (Finset.filter_subset_filter _ hsub)
  have hZS : ZS ⊆ ZC := Finset.image_subset_image (Finset.image_subset_image hDS)
  have hne : ZS.Nonempty := ((prefixFiber_nonempty hp₀).image _).image _ |>.image _
  have hret := blockClass_child_retention hL hL' B f g K p q hsub hM hmass hji hi hp₀
  change (DC.card:ℝ) ≤ (M*(2:ℝ)^(2*i+2*j))*(DS.card:ℝ) at hret
  have hcount : (ZC.card:ℝ) ≤ (M*(2:ℝ)^(2*i+2*j))*(ZS.card:ℝ) := by
    change ZC.card = DC.card at hcC
    change ZS.card = DS.card at hcS
    simpa only [hcC,hcS] using hret
  refine ⟨hne,hZS,hchart,hsep,hcount,?_⟩
  intro s A hA hball
  exact normalized_finite_ball_bound_subset (by positivity) hA hZS hcount hball

end Falconer

end OAI
