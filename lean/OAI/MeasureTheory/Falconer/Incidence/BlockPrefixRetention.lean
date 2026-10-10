import OAI.MeasureTheory.Falconer.Estimates.PrefixRetention
import OAI.MeasureTheory.Falconer.Incidence.BlockLeafCounts

namespace OAI

/-! After a second block regularization, a large retained class has mass
in each occupied parent comparable to that of the original class. -/
namespace Falconer.Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_prefix_retention {N : ℕ}
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).card:ℝ) ≤
      M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    {i : ℕ} (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i))) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) ≤
      (M*(2:ℝ)^(2*i))*((prefixFiber S (blockDepth N B i) p₀).card:ℝ) := by
  have hret := prefix_fiber_local_retention
    (b := (blockProduct L (blockLabel L N B f K) N B i p:ℝ))
    _ _ (blockDepth N B i) hsub hM
    (by positivity : 0 ≤ (2:ℝ)^i) (by positivity : 0 ≤ (2:ℝ)^i)
    (Nat.cast_nonneg (blockProduct L' (blockLabel L' N B g K) N B i q)) hmass
    (fun r hr => by exact_mod_cast blockClass_leaf_count hL B f K p hi hr)
    (fun r hr => by exact_mod_cast blockClass_leaf_count hL' B g K q hi hr) hp₀
  convert hret using 1
  rw [show 2*i = i+i by omega,pow_add]
  ring

end Falconer.Regularization

end OAI
