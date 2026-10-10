import OAI.MeasureTheory.Falconer.Incidence.BlockPrefixRetention

namespace OAI

/-! A recursive restriction pays for its loss within the current parent,
not for the number of unrelated parents in the original configuration. -/
namespace Falconer.Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_parent_prefix_retention {N a : ℕ}
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q r : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a r)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((prefixFiber
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a r).card:ℝ) ≤
        M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    {i : ℕ} (hi : i ≤ K) (ha : a ≤ blockDepth N B i) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i))) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) ≤
      (M*(2:ℝ)^(2*i))*((prefixFiber S (blockDepth N B i) p₀).card:ℝ) := by
  let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
  let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
  let C₀ := prefixFiber C a r
  have hC₀ : C₀ ⊆ C := Finset.filter_subset _ _
  have hprefix (u : CellPath 2) (hu : u ∈ C₀.image (List.take (blockDepth N B i))) :
      prefixFiber C₀ (blockDepth N B i) u = prefixFiber C (blockDepth N B i) u :=
    prefixFiber_parent_filter ha hu
  have hret := prefix_fiber_local_retention
    (b := (blockProduct L (blockLabel L N B f K) N B i p:ℝ))
    C₀ S (blockDepth N B i) hsub hM
    (by positivity : 0 ≤ (2:ℝ)^i) (by positivity : 0 ≤ (2:ℝ)^i)
    (Nat.cast_nonneg (blockProduct L' (blockLabel L' N B g K) N B i q)) hmass
    (fun u hu => by
      rw [hprefix u hu]
      exact_mod_cast blockClass_leaf_count hL B f K p hi (Finset.image_subset_image hC₀ hu))
    (fun u hu => by exact_mod_cast blockClass_leaf_count hL' B g K q hi hu) hp₀
  rw [hprefix p₀ (Finset.image_subset_image hsub hp₀)] at hret
  convert hret using 1
  rw [show 2*i = i+i by omega,pow_add]
  ring

end Falconer.Regularization

end OAI
