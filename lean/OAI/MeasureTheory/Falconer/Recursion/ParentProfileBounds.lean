import OAI.MeasureTheory.Falconer.Geometry.ParentEndpointGeometry
import OAI.MeasureTheory.Falconer.Recursion.RetainedProfileBounds
import OAI.MeasureTheory.Falconer.Estimates.QuarterEndpointMap

namespace OAI

/-! Reference-profile bounds persist below an active parent and in the
fixed quarter chart used by the actual scale-product construction. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_parent_endpoint_ball {N a₀ : ℕ} (hN : 0 < N)
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q r₀ : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a₀ r₀)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((prefixFiber (classLeaves L (blockLabel L N B f K)
      (blockLabel L N B f K p)) a₀ r₀).card:ℝ) ≤
        M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) (ha₀ : a₀ ≤ blockDepth N B i) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)))
    {s A : ℝ} (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤
        (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))) :
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let C := (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)*(M*(2:ℝ)^(2*i+2*j))
    let Z := blockEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
    Z.Nonempty ∧ InBoundedLineChart Z ∧
      FiniteSeparatedAt (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i)) Z ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i)) s C Z ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i+2)) s
        ((max 1 C)*4^s)
        (quarterEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀) := by
  have hsubC := hsub.trans (Finset.filter_subset _ _)
  have hpC := Finset.image_subset_image hsubC hp₀
  obtain ⟨_,_,hball⟩ := blockClass_truncated_local_ball hN hL B f K p Q hQ hji hi hpC
    hs hA hprofile ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1)
  obtain ⟨hne,_,hchart,hsep,_,htransfer⟩ := blockClass_parent_endpoint_geometry
    hL hL' B f g K p q r₀ hsub hM hmass Q hQ hji hi ha₀ hp₀
  have hretained := htransfer s _ (by positivity) hball
  refine ⟨hne,hchart,hsep,hretained,?_⟩
  rw [quarterEndpointSet_eq]
  have he : (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i))/4 =
      1/(2:ℝ)^(blockDepth N B j-blockDepth N B i+2) := by
    rw [pow_add]
    norm_num
    ring
  rw [← he]
  apply planarQuarter_regular (by positivity) hs (le_max_left _ _)
  exact normalizedFiniteBallBound_mono_constant (by positivity) (le_max_right _ _) hretained

end Falconer

end OAI
