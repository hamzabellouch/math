import OAI.MeasureTheory.Falconer.Incidence.BlockDescendantCounts

namespace OAI

/-! Local covering numbers and fiber ratios expressed in the actual
branching profile, for the regular-scale incidence argument. -/
namespace Falconer.Regularization
variable {d : ℕ}

theorem blockProduct_relative_profile {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ)
    (B K : ℕ) (p : CellPath d) {i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) :
    (blockProduct L F N B i p : ℝ)/(blockProduct L F N B j p : ℝ) =
      (2 : ℝ)^((N : ℝ)*(regularizedProfile L F N B K p (blockDepth N B j)-
        regularizedProfile L F N B K p (blockDepth N B i))) := by
  rw [blockProduct_profile_difference hN hL F B K p hi,
    blockProduct_profile_difference hN hL F B K p hj,
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem blockClass_local_covering_count {N : ℕ} (hN : 0 < N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ)
    (p : CellPath d) {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    let T := prefixChildren C (blockDepth N B i) (blockDepth N B j) P
    let X := (N : ℝ)*(regularizedProfile L F N B K p (blockDepth N B j)-
      regularizedProfile L F N B K p (blockDepth N B i))
    (2 : ℝ)^X/(2 : ℝ)^j ≤ T.card ∧ (T.card : ℝ) ≤ (2 : ℝ)^i*(2 : ℝ)^X := by
  have hb := blockClass_descendant_count hL B f K p hji hi hP
  dsimp only at hb ⊢
  rw [blockProduct_relative_profile hN hL _ B K p hi (hji.trans hi)] at hb
  exact hb

theorem blockClass_fiber_ratio {N : ℕ} {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ)
    (p : CellPath d) {i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) {P Q : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i)))
    (hQ : Q ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B j))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    ((prefixFiber C (blockDepth N B j) Q).card : ℝ)/
      ((prefixFiber C (blockDepth N B i) P).card : ℝ) ≤
        (2 : ℝ)^j*((blockProduct L F N B j p : ℝ)/(blockProduct L F N B i p : ℝ)) := by
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  have hparent := blockClass_leaf_count hL B f K p hi hP
  have hchild := blockClass_leaf_count hL B f K p hj hQ
  have hp : (blockProduct L F N B i p : ℝ) ≤ ((prefixFiber C (blockDepth N B i) P).card : ℝ) := by
    exact_mod_cast hparent.1
  have hq : ((prefixFiber C (blockDepth N B j) Q).card : ℝ) ≤
      (2 : ℝ)^j*(blockProduct L F N B j p : ℝ) := by exact_mod_cast hchild.2
  have hpos : 0 < (blockProduct L F N B i p : ℝ) := by exact_mod_cast blockProduct_pos L F N B i p
  have hr := div_le_div₀
    (show 0 ≤ (2 : ℝ)^j*(blockProduct L F N B j p : ℝ) by positivity) hq hpos hp
  simpa only [mul_div_assoc] using hr

theorem blockClass_local_fiber_profile {N : ℕ} (hN : 0 < N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ)
    (p : CellPath d) {i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) {P Q : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i)))
    (hQ : Q ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B j))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    ((prefixFiber C (blockDepth N B j) Q).card : ℝ)/
      ((prefixFiber C (blockDepth N B i) P).card : ℝ) ≤
        (2 : ℝ)^j*(2 : ℝ)^((N : ℝ)*(regularizedProfile L F N B K p (blockDepth N B i)-
          regularizedProfile L F N B K p (blockDepth N B j))) := by
  have hb := blockClass_fiber_ratio hL B f K p hi hj hP hQ
  dsimp only at hb ⊢
  rw [blockProduct_relative_profile hN hL _ B K p hj hi] at hb
  exact hb

end Falconer.Regularization

end OAI
