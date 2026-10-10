import OAI.MeasureTheory.Falconer.Recursion.LocalProfileCounts

namespace OAI

/-! The two directions of the profile/regularity dictionary: a lower chord
bound gives local nonconcentration, and an upper chord bound gives covering. -/
namespace Falconer.Regularization
variable {d : ℕ}

theorem blockClass_local_frostman {N : ℕ} (hN : 0 < N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ)
    (p : CellPath d) {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {P Q : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i)))
    (hQ : Q ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B j))) {s A : ℝ}
    (hprofile : let F := blockLabel L N B f K
      s*((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))-A ≤
        (N : ℝ)*(regularizedProfile L F N B K p (blockDepth N B j)-
          regularizedProfile L F N B K p (blockDepth N B i))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    ((prefixFiber C (blockDepth N B j) Q).card : ℝ)/
      ((prefixFiber C (blockDepth N B i) P).card : ℝ) ≤
      (2 : ℝ)^j*(2 : ℝ)^(A-s*((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))) := by
  have hb := blockClass_local_fiber_profile hN hL B f K p hi (hji.trans hi) hP hQ
  dsimp only at hprofile hb ⊢
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith

theorem blockClass_local_covering {N : ℕ} (hN : 0 < N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ)
    (p : CellPath d) {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i))) {s A : ℝ}
    (hprofile : let F := blockLabel L N B f K
      (N : ℝ)*(regularizedProfile L F N B K p (blockDepth N B j)-
        regularizedProfile L F N B K p (blockDepth N B i)) ≤
          s*((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))+A) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    ((prefixChildren C (blockDepth N B i) (blockDepth N B j) P).card : ℝ) ≤
      (2 : ℝ)^i*(2 : ℝ)^(s*((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))+A) := by
  have hb := (blockClass_local_covering_count hN hL B f K p hji hi hP).2
  dsimp only at hprofile hb ⊢
  exact hb.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hprofile) (by positivity))

end Falconer.Regularization

end OAI
