import OAI.MeasureTheory.Falconer.Estimates.RefinedEndpointSelection

namespace OAI

/-! A selected endpoint configuration can be regularized again while keeping
the original reference profile and an explicit loss in the new active parent. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_parent_refine_quarter_endpoint_subset {N a₀ : ℕ}
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q r₀ : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a₀ r₀)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((prefixFiber (classLeaves L (blockLabel L N B f K)
      (blockLabel L N B f K p)) a₀ r₀).card:ℝ) ≤
        M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) (ha₀ : a₀ ≤ blockDepth N B i) (p₀ : CellPath 2)
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)))
    (P : Finset (Space 2)) (hP : P.Nonempty)
    (hPsub : P ⊆ quarterEndpointSet Q
      (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q))
      (blockDepth N B i) (blockDepth N B j) p₀)
    {H : ℝ} (hH : 0 ≤ H)
    (hsize : ((quarterEndpointSet Q
      (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q))
      (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤ H*(P.card:ℝ)) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let M' := (M*(2:ℝ)^(2*i))*((H*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K)
    ∃ E ⊆ prefixFiber S (blockDepth N B i) p₀, E ⊆ cubePaths 2 N ∧
      E ⊆ prefixFiber C (blockDepth N B i) p₀ ∧ ∃ u ∈ E,
        let T := classLeaves E (blockLabel E N B (fun _ => []) K)
          (blockLabel E N B (fun _ => []) K u)
        T ⊆ E ∧ T.Nonempty ∧
          ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) ≤ M'*(T.card:ℝ) ∧
          quarterEndpointSet Q T (blockDepth N B i) (blockDepth N B j) p₀ ⊆ P := by
  obtain ⟨E,hE,hEN,u,hu,hT,hTne,hmassT,hTP⟩ :=
    blockClass_refine_quarter_endpoint_subset hL' B g K q Q hQ hji hi p₀ P hP hPsub hH hsize
  have hEC := hE.trans (Finset.filter_subset_filter _ (hsub.trans (Finset.filter_subset _ _)))
  have hparent := blockClass_parent_prefix_retention hL hL' B f g K p q r₀
    hsub hM hmass hi ha₀ hp₀
  refine ⟨E,hE,hEN,hEC,u,hu,hT,hTne,?_,hTP⟩
  calc
    _ ≤ (M*(2:ℝ)^(2*i))*
        ((prefixFiber (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q))
          (blockDepth N B i) p₀).card:ℝ) := hparent
    _ ≤ (M*(2:ℝ)^(2*i))*(((H*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K)*
        ((classLeaves E (blockLabel E N B (fun _ => []) K)
          (blockLabel E N B (fun _ => []) K u)).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hmassT (by positivity)
    _ = _ := by ring

end Falconer

end OAI
