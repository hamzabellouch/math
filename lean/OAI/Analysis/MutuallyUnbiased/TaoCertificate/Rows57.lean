import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source456 : Sparse := [([0, -2, -1, 0, 1, 1, 1], 9), ([0, -2, -1, 0, 2, 0, 1], 9), ([0, -2, -1, 1, 1, 0, 1], -9), ([0, -2, 0, 0, 1, 0, 1], 9), ([0, -1, -2, 0, 1, 1, 1], 9), ([0, -1, -2, 1, 1, 0, 1], 9), ([0, -1, -1, 0, 0, 0, 2], 18), ([0, -1, -1, 0, 2, -1, 1], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, 0, -1, -1, 1, 0, 1], 9), ([0, 0, -1, 0, 1, -1, 1], 9), ([1, -2, -1, 0, 1, 1, 1], 9), ([1, -2, 0, 0, 1, 0, 1], 9), ([1, -1, -2, 0, 1, 1, 1], 9), ([1, -1, -2, 0, 2, 0, 1], 9), ([1, -1, -2, 1, 1, 0, 1], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 2, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], 18), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, 0, -1, 1, 0, 1], 9), ([1, 0, -2, 0, 1, 0, 1], -9), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, -1, 0, 1, 0, 0], 9)]

theorem source456_checked : normalize (row ![-1, -1, 0, 1, 0, 1] ![0, 0, 0, 1, 0, -1] (3, 3)) = source456 := by
  decide +kernel

theorem source456_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source456 (momentValues f) = 0 := by
  rw [← source456_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source457 : Sparse := [([0, 0, 1, 0, -1, 0, 0], -9), ([0, 0, 2, 0, -1, 0, -1], 9), ([0, 1, 0, 0, -1, 0, 0], 9), ([0, 1, 0, 0, -1, 1, -1], -9), ([0, 1, 1, -1, -1, 0, 0], 9), ([0, 1, 1, 0, -2, 1, -1], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 1, 1, 1, -2, 0, -1], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 2, 0, -2, 0, -1], -9), ([0, 2, 1, -1, -1, 0, -1], -9), ([0, 2, 1, 0, -2, 0, -1], 9), ([1, 0, 1, 0, -1, 0, 0], -9), ([1, 0, 1, 0, -1, 1, -1], -9), ([1, 0, 1, 1, -1, 0, -1], -9), ([1, 0, 2, 0, -1, 0, -1], 9), ([1, 1, 0, 1, -1, 0, -1], -9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 1, 1, 0, 0, 0, -2], -18), ([1, 1, 1, 1, -2, 0, -1], -9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 2, -1, -1, 0, -1], -9), ([1, 1, 2, 0, -2, 0, -1], -9), ([1, 1, 2, 0, -1, -1, -1], -9), ([1, 2, 0, 0, -1, 0, -1], -9), ([1, 2, 1, 0, -1, -1, -1], -9)]

theorem source457_checked : normalize (row ![1, 1, 0, -1, 0, -1] ![0, 0, 0, -1, 0, 1] (0, -3)) = source457 := by
  decide +kernel

theorem source457_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source457 (momentValues f) = 0 := by
  rw [← source457_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source458 : Sparse := [([0, -2, 0, -1, 2, 0, 1], -9), ([0, -2, 0, 0, 1, 0, 1], 9), ([0, -1, -1, -1, 2, 0, 1], 9), ([0, -1, 0, -2, 1, 1, 1], -9), ([0, -1, 0, -2, 2, 0, 1], 9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 0, -1, 2, -1, 1], -9), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, 0, -1, 1, 0, 0], 9), ([1, -2, 0, -1, 1, 1, 1], -9), ([1, -2, 0, -1, 2, 0, 1], -9), ([1, -2, 0, 0, 1, 0, 1], 9), ([1, -2, 1, -1, 1, 0, 1], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, 0, -1, 0, 0, 2], -18), ([1, -1, 0, -1, 2, -1, 1], -9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 1, -2, 1, 0, 1], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, 0, 0, -2, 1, 0, 1], -9), ([1, 0, 0, -1, 1, -1, 1], -9)]

theorem source458_checked : normalize (row ![-1, 0, -1, 1, 0, 1] ![0, 0, 0, 1, 0, -1] (0, -3)) = source458 := by
  decide +kernel

theorem source458_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source458 (momentValues f) = 0 := by
  rw [← source458_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source459 : Sparse := [([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 0, 1, -1, 1, -1], 9), ([0, 0, 0, 2, -1, 0, -1], 9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 1, -1, 2, -1, 0, -1], 9), ([0, 1, 0, 0, -1, 1, -1], 9), ([0, 1, 0, 1, -1, -1, 0], 9), ([0, 1, 0, 1, 0, 0, -2], 18), ([0, 1, 0, 2, -2, 0, -1], 9), ([0, 1, 0, 2, -1, -1, -1], -9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 1, 1, 1, -2, 0, -1], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 2, -1, 1, -1, 0, -1], 9), ([0, 2, 0, 1, -1, -1, -1], 9), ([1, 0, 0, 1, -1, 1, -1], 9), ([1, 0, 0, 2, -1, 0, -1], 9), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 2, -1, 0, -1], 9), ([1, 1, 0, 0, -1, 0, 0], 9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 1, 0, 1, -2, 1, -1], 9), ([1, 1, 0, 1, 0, 0, -2], 18), ([1, 1, 1, 0, -1, 0, -1], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 2, -1, 1, -1, 0, -1], 9), ([1, 2, 0, 0, -1, 0, -1], -9), ([1, 2, 0, 1, -2, 0, -1], 9), ([1, 2, 0, 1, -1, -1, -1], 9)]

theorem source459_checked : normalize (row ![1, 0, 1, -1, 0, -1] ![0, 0, 0, -1, 0, 1] (3, 3)) = source459 := by
  decide +kernel

theorem source459_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source459 (momentValues f) = 0 := by
  rw [← source459_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source460 : Sparse := [([0, -2, 0, 0, 1, 0, 1], 9), ([0, -2, 0, 0, 2, -1, 1], 9), ([0, -2, 0, 1, 1, -1, 1], -9), ([0, -2, 1, 0, 1, -1, 1], 9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, 0, 0, 0, -1, 2], 18), ([0, -1, 0, 0, 2, -2, 1], 9), ([0, -1, 0, 1, 1, -2, 1], 9), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, 0, 1, -2, 1], -9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 0, 0, 1, -2, 1], 9), ([1, -2, 0, 0, 1, 0, 1], 9), ([1, -2, 1, 0, 1, -1, 1], 9), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, -1, 0, 2, -1, 1], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 0, -1, 2, -1, 1], 9), ([1, -1, 0, 0, 0, -1, 2], 18), ([1, -1, 0, 0, 1, 0, 0], 9), ([1, -1, 0, 1, 1, -2, 1], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, 0, -1, 0, 1, -1, 1], -9), ([1, 0, 0, -1, 1, -1, 1], 9), ([1, 0, 0, 0, 1, -2, 1], 9), ([1, 0, 0, 0, 1, -1, 0], 9)]

theorem source460_checked : normalize (row ![-1, 0, 0, 1, -1, 1] ![0, 0, 0, 1, 0, -1] (3, 3)) = source460 := by
  decide +kernel

theorem source460_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source460 (momentValues f) = 0 := by
  rw [← source460_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source461 : Sparse := [([0, 0, 0, 0, -1, 1, 0], -9), ([0, 0, 1, 0, -1, 1, -1], 9), ([0, 1, -1, 0, -1, 1, 0], 9), ([0, 1, -1, 0, -1, 2, -1], -9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 1, 0, 0, -2, 2, -1], 9), ([0, 1, 0, 0, -1, 0, 0], -9), ([0, 1, 0, 1, -2, 1, -1], -9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 1, 1, 0, -2, 1, -1], -9), ([0, 2, 0, -1, -1, 1, -1], -9), ([0, 2, 0, 0, -2, 1, -1], 9), ([1, 0, 0, 0, -1, 1, 0], -9), ([1, 0, 0, 0, -1, 2, -1], -9), ([1, 0, 0, 1, -1, 1, -1], -9), ([1, 0, 1, 0, -1, 1, -1], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, 0, -1, -1, 2, -1], -9), ([1, 1, 0, 0, -1, 0, 0], -9), ([1, 1, 0, 0, 0, 1, -2], -18), ([1, 1, 0, 1, -2, 1, -1], -9), ([1, 1, 0, 1, -1, 0, -1], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, 0, -2, 1, -1], -9), ([1, 1, 1, 0, -1, 0, -1], -9), ([1, 2, -1, 0, -1, 1, -1], -9), ([1, 2, 0, 0, -1, 0, -1], -9)]

theorem source461_checked : normalize (row ![1, 0, 0, -1, 1, -1] ![0, 0, 0, -1, 0, 1] (0, -3)) = source461 := by
  decide +kernel

theorem source461_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source461 (momentValues f) = 0 := by
  rw [← source461_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source462 : Sparse := [([0, -1, -1, -1, 2, 0, 1], -9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, 0, -2, -1, 2, 0, 1], 9), ([0, 0, -1, -2, 1, 1, 1], -9), ([0, 0, -1, -2, 2, 0, 1], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, -1, -1, 2, -1, 1], -9), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 1, -2, -1, 1, 0, 1], -9), ([0, 1, -1, -1, 1, 0, 0], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 2, 0, 1], -9), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, 0, -1, 1, 0, 1], -9), ([1, 0, -2, -1, 1, 1, 1], -9), ([1, 0, -2, 0, 1, 0, 1], -9), ([1, 0, -1, -1, 0, 0, 2], -18), ([1, 0, -1, -1, 2, -1, 1], -9), ([1, 0, -1, 0, 1, -1, 1], -9), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, 0, -2, 1, 0, 1], -9), ([1, 0, 0, -1, 1, -1, 1], 9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 1, -1, -2, 1, 0, 1], -9), ([1, 1, -1, -1, 1, -1, 1], -9)]

theorem source462_checked : normalize (row ![0, -1, -1, 1, 0, 1] ![0, 0, 0, 1, 0, -1] (0, -3)) = source462 := by
  decide +kernel

theorem source462_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source462 (momentValues f) = 0 := by
  rw [← source462_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source463 : Sparse := [([0, -1, 1, 1, -1, 0, 0], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 2, -1, 0, -1], 9), ([0, -1, 2, 1, -1, 0, -1], -9), ([0, 0, 0, 2, -1, 0, -1], 9), ([0, 0, 1, 0, -1, 1, -1], 9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 0, 1, 1, 0, 0, -2], 18), ([0, 0, 1, 2, -2, 0, -1], 9), ([0, 0, 1, 2, -1, -1, -1], -9), ([0, 0, 2, 0, -1, 0, -1], 9), ([0, 0, 2, 1, -2, 0, -1], 9), ([0, 0, 2, 1, -1, -1, -1], 9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 2, -1, 0, -1], 9), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 0, 0, 1, -1, 1, -1], -9), ([1, 0, 0, 2, -1, 0, -1], 9), ([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 1, 0, -1, 1, -1], 9), ([1, 0, 1, 1, -2, 1, -1], 9), ([1, 0, 1, 1, 0, 0, -2], 18), ([1, 0, 2, 0, -1, 0, -1], 9), ([1, 0, 2, 1, -1, -1, -1], 9), ([1, 1, 0, 1, -1, 0, -1], 9), ([1, 1, 1, 0, -1, 0, -1], -9), ([1, 1, 1, 1, -2, 0, -1], 9), ([1, 1, 1, 1, -1, -1, -1], 9)]

theorem source463_checked : normalize (row ![0, 1, 1, -1, 0, -1] ![0, 0, 0, -1, 0, 1] (3, 3)) = source463 := by
  decide +kernel

theorem source463_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source463 (momentValues f) = 0 := by
  rw [← source463_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
