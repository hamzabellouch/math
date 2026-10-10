import OAI.MeasureTheory.Falconer.Estimates.ChildRetention
import OAI.MeasureTheory.Falconer.Estimates.ParentPrefixRetention

namespace OAI

/-! Endpoint retention after restricting inside one actual recursive parent. -/
namespace Falconer.Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem blockClass_parent_child_retention {N a : ℕ}
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q r₀ : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a r₀)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a r₀).card:ℝ) ≤
      M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) (ha : a ≤ blockDepth N B i) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i))) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    ((prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤
      (M*(2:ℝ)^(2*i+2*j))*
        ((prefixChildren S (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) := by
  let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
  let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
  have hsubC : S ⊆ C := hsub.trans (Finset.filter_subset _ _)
  let u : ℝ := blockProduct L (blockLabel L N B f K) N B j p
  let v : ℝ := blockProduct L' (blockLabel L' N B g K) N B j q
  have hu : 0 < u := Nat.cast_pos.mpr (blockProduct_pos _ _ _ _ _ _)
  have hc (r : CellPath 2) (hr : r ∈ C.image (List.take (blockDepth N B j))) :
      u ≤ ((prefixFiber C (blockDepth N B j) r).card:ℝ) ∧
      ((prefixFiber C (blockDepth N B j) r).card:ℝ) ≤ (2:ℝ)^j*u := by
    dsimp only [u,C]
    exact_mod_cast blockClass_leaf_count hL B f K p (hji.trans hi) hr
  have hs (r : CellPath 2) (hr : r ∈ S.image (List.take (blockDepth N B j))) :
      v ≤ ((prefixFiber S (blockDepth N B j) r).card:ℝ) ∧
      ((prefixFiber S (blockDepth N B j) r).card:ℝ) ≤ (2:ℝ)^j*v := by
    dsimp only [v,S]
    exact_mod_cast blockClass_leaf_count hL' B g K q (hji.trans hi) hr
  obtain ⟨z,hz⟩ := prefixFiber_nonempty hp₀
  let r := z.take (blockDepth N B j)
  have hrS : r ∈ S.image (List.take (blockDepth N B j)) :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.mp hz).1
  have hrC : r ∈ C.image (List.take (blockDepth N B j)) := Finset.image_subset_image hsubC hrS
  have hvu : v ≤ (2:ℝ)^j*u := by
    apply (hs r hrS).1.trans
    apply le_trans _ (hc r hrC).2
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hsubC)
  have hCmass := (prefix_children_mass_bounds C (blockDepth_antitone N B hji) p₀
    (fun r hr => hc r (prefixChildren_mem_image hr))).1
  have hSmass := (prefix_children_mass_bounds S (blockDepth_antitone N B hji) p₀
    (fun r hr => hs r (prefixChildren_mem_image hr))).2
  have hretain := blockClass_parent_prefix_retention hL hL' B f g K p q r₀ hsub hM hmass hi ha hp₀
  apply (mul_le_mul_iff_left₀ hu).1
  calc
    _ ≤ ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) := hCmass
    _ ≤ (M*(2:ℝ)^(2*i))*((prefixFiber S (blockDepth N B i) p₀).card:ℝ) := hretain
    _ ≤ (M*(2:ℝ)^(2*i))*
        (((prefixChildren S (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ)*((2:ℝ)^j*v)) :=
      mul_le_mul_of_nonneg_left hSmass (by positivity)
    _ ≤ (M*(2:ℝ)^(2*i))*
        (((prefixChildren S (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ)*((2:ℝ)^j*((2:ℝ)^j*u))) := by
      gcongr
    _ = _ := by
      rw [pow_add,pow_mul]
      ring


end Falconer.Regularization

end OAI
