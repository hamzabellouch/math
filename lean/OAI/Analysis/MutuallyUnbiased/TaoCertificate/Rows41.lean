import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source328 : Sparse := [([0, -2, 0, 1, 1, 1, -1], -9), ([0, -2, 0, 2, 1, 0, -1], 9), ([0, -1, -1, 2, 1, 0, -1], -9), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 1, 0, 1, -1], 9), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, -1, 0, 2, 1, -1, -1], -9), ([0, -1, 0, 2, 1, 0, -2], 9), ([0, -1, 1, 1, 0, 0, -1], 9), ([0, -1, 1, 1, 1, 0, -2], -9), ([0, 0, -1, 1, 1, 0, -1], 9), ([0, 0, 0, 1, 0, 0, -1], -9), ([1, -2, 0, 1, 1, 0, 0], -9), ([1, -2, 1, 1, 1, 0, -1], -9), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 2, 1, 0, -1], -9), ([1, -1, 0, 0, 2, 0, -1], -18), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 0, 1, 1, 1, -2], -9), ([1, -1, 0, 2, 1, -1, -1], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 1, 1, -1, -1], -9), ([1, 0, 0, 1, 1, 0, -2], -9)]

theorem source328_checked : normalize (row ![-1, 0, 1, 1, 0, -1] ![0, 0, 1, -1, 0, 0] (0, -3)) = source328 := by
  decide +kernel

theorem source328_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source328 (momentValues f) = 0 := by
  rw [← source328_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source329 : Sparse := [([0, 0, 0, -1, -1, 0, 2], 9), ([0, 0, 0, -1, -1, 1, 1], 9), ([0, 1, -1, -1, -1, 0, 2], -9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 0, 0, 1], 9), ([0, 1, 0, -2, -1, 0, 2], 9), ([0, 1, 0, -1, -1, -1, 2], 9), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 1, 0, 0, -2, 0, 1], 18), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, -1, 0, 0], 9), ([0, 2, -1, -1, -1, 0, 1], 9), ([0, 2, 0, -2, -1, 0, 1], 9), ([0, 2, 0, -1, -1, -1, 1], -9), ([0, 2, 0, -1, -1, 0, 0], 9), ([1, 0, 0, -1, -1, 0, 2], 9), ([1, 0, 0, -1, -1, 1, 1], 9), ([1, 0, 0, -1, 0, 0, 1], 9), ([1, 0, 1, -1, -1, 0, 1], -9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, 0, -2, -1, 1, 1], 9), ([1, 1, 0, -1, -1, -1, 2], 9), ([1, 1, 0, -1, -1, 1, 0], -9), ([1, 1, 0, -1, 0, 0, 0], 9), ([1, 1, 0, 0, -2, 0, 1], 18), ([1, 1, 1, -2, -1, 0, 1], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, 0, 0], 9), ([1, 2, -1, -1, -1, 0, 1], 9), ([1, 2, 0, -1, -1, 0, 0], 9)]

theorem source329_checked : normalize (row ![1, 0, -1, -1, 0, 1] ![0, 0, -1, 1, 0, 0] (3, 3)) = source329 := by
  decide +kernel

theorem source329_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source329 (momentValues f) = 0 := by
  rw [← source329_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source330 : Sparse := [([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, 0, -2, 1, 1, -1, 1], 9), ([0, 0, -2, 1, 1, 0, 0], 9), ([0, 0, -2, 2, 1, -1, 0], 9), ([0, 0, -1, 0, 2, -1, 0], 18), ([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, -1, 1, 1, -2, 1], -9), ([0, 0, -1, 1, 1, 0, -1], 9), ([0, 0, -1, 2, 1, -2, 0], 9), ([0, 0, 0, 1, 1, -2, 0], 9), ([0, 1, -2, 1, 1, -1, 0], -9), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 1, -1, 1, 1, -2, 0], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 2, 1, -1, 0], 9), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, 0, -2, 1, 1, -1, 1], 9), ([1, 0, -2, 1, 1, 0, 0], 9), ([1, 0, -1, 0, 2, -1, 0], 18), ([1, 0, -1, 1, 0, 0, 0], 9), ([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, -1, 2, 1, -1, -1], 9), ([1, 0, 0, 1, 0, -1, 0], 9), ([1, 0, 0, 1, 1, -2, 0], 9), ([1, 0, 0, 1, 1, -1, -1], -9), ([1, 1, -1, 1, 1, -2, 0], 9), ([1, 1, -1, 1, 1, -1, -1], 9)]

theorem source330_checked : normalize (row ![0, -1, 1, 1, -1, 0] ![0, 0, 1, -1, 0, 0] (3, 3)) = source330 := by
  decide +kernel

theorem source330_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source330 (momentValues f) = 0 := by
  rw [← source330_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source331 : Sparse := [([0, -1, 1, -1, 0, 1, 0], 9), ([0, -1, 2, -1, -1, 1, 0], -9), ([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 0, -1, 0, 1, 0], -9), ([0, 0, 1, -2, -1, 1, 1], -9), ([0, 0, 1, -2, -1, 2, 0], 9), ([0, 0, 1, -1, -1, 2, -1], -9), ([0, 0, 1, -1, 0, 0, 0], -9), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 0, 2, -2, -1, 1, 0], 9), ([0, 1, 1, -2, -1, 1, 0], -9), ([0, 1, 1, -1, -1, 0, 0], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, -1, 2, 0], -9), ([1, 0, 0, -1, -1, 1, 1], 9), ([1, 0, 0, -1, -1, 2, 0], -9), ([1, 0, 0, -1, 0, 1, 0], -9), ([1, 0, 1, -2, -1, 1, 1], -9), ([1, 0, 1, -1, -1, 0, 1], -9), ([1, 0, 1, -1, 0, 0, 0], -9), ([1, 0, 1, 0, -2, 1, 0], -18), ([1, 0, 2, -1, -1, 0, 0], -9), ([1, 0, 2, -1, -1, 1, -1], -9), ([1, 1, 0, -1, -1, 1, 0], -9), ([1, 1, 1, -2, -1, 1, 0], -9), ([1, 1, 1, -1, -1, 0, 0], 9), ([1, 1, 1, -1, -1, 1, -1], -9)]

theorem source331_checked : normalize (row ![0, 1, -1, -1, 1, 0] ![0, 0, -1, 1, 0, 0] (0, -3)) = source331 := by
  decide +kernel

theorem source331_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source331 (momentValues f) = 0 := by
  rw [← source331_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source332 : Sparse := [([0, -1, -1, 1, 1, 0, 0], 9), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, 0, -2, 1, 1, 0, 0], 9), ([0, 0, -2, 1, 1, 1, -1], 9), ([0, 0, -2, 2, 1, 0, -1], 9), ([0, 0, -1, 0, 2, 0, -1], 18), ([0, 0, -1, 1, 0, 0, 0], 9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, -1, 1, 1, 1, -2], 9), ([0, 0, -1, 2, 1, -1, -1], 9), ([0, 0, 0, 1, 1, -1, -1], 9), ([0, 1, -2, 1, 1, 0, -1], -9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, -1, 1, 1, 0, -2], 9), ([1, -1, -1, 1, 1, 0, 0], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 2, 1, 0, -1], 9), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, 0, -2, 1, 1, 0, 0], 9), ([1, 0, -2, 1, 1, 1, -1], 9), ([1, 0, -1, 0, 2, 0, -1], 18), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 0, -1, 1, 1, 1, -2], 9), ([1, 0, -1, 2, 1, 0, -2], 9), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 0, 0, 1, 1, -1, -1], 9), ([1, 0, 0, 1, 1, 0, -2], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 1, 1, 0, -2], 9)]

theorem source332_checked : normalize (row ![0, -1, 1, 1, 0, -1] ![0, 0, 1, -1, 0, 0] (3, 3)) = source332 := by
  decide +kernel

theorem source332_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source332 (momentValues f) = 0 := by
  rw [← source332_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source333 : Sparse := [([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 2, -1, -1, 0, 1], -9), ([0, 0, 0, -1, -1, 0, 2], 9), ([0, 0, 0, -1, 0, 0, 1], -9), ([0, 0, 1, -2, -1, 0, 2], -9), ([0, 0, 1, -2, -1, 1, 1], 9), ([0, 0, 1, -1, -1, 1, 0], -9), ([0, 0, 1, -1, 0, -1, 1], -9), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 2, -2, -1, 0, 1], 9), ([0, 1, 1, -2, -1, 0, 1], -9), ([0, 1, 1, -1, -1, -1, 1], 9), ([1, -1, 1, -1, -1, 0, 2], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, 0, 0, -1, -1, 0, 2], 9), ([1, 0, 0, -1, -1, 1, 1], -9), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 1, -2, -1, 0, 2], -9), ([1, 0, 1, -1, -1, -1, 2], -9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 0, 1, 0, -2, 0, 1], -18), ([1, 0, 2, -1, -1, -1, 1], -9), ([1, 0, 2, -1, -1, 0, 0], -9), ([1, 1, 0, -1, -1, 0, 1], -9), ([1, 1, 1, -2, -1, 0, 1], -9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, 0, 0], -9)]

theorem source333_checked : normalize (row ![0, 1, -1, -1, 0, 1] ![0, 0, -1, 1, 0, 0] (0, -3)) = source333 := by
  decide +kernel

theorem source333_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source333 (momentValues f) = 0 := by
  rw [← source333_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source334 : Sparse := [([0, -1, 0, 1, 1, 0, -1], -9), ([0, -1, 0, 2, 1, -1, -1], 9), ([0, 0, -1, 2, 1, -1, -1], -9), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 0, 0, 1, 0, 0, -1], 9), ([0, 0, 0, 1, 1, -2, 0], 9), ([0, 0, 0, 2, 1, -2, -1], -9), ([0, 0, 0, 2, 1, -1, -2], 9), ([0, 0, 1, 1, 0, -1, -1], 9), ([0, 0, 1, 1, 1, -1, -2], -9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 0, -1, 1, 1, 0, -1], -9), ([1, 0, -1, 2, 1, -1, -1], -9), ([1, 0, 0, 0, 2, -1, -1], -18), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 0, 0, 1, 1, -2, 0], 9), ([1, 0, 0, 1, 1, 0, -2], -9), ([1, 0, 0, 2, 1, -2, -1], -9), ([1, 0, 1, 1, 1, -2, -1], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 1, 0, 1, 1, -2, -1], -9), ([1, 1, 0, 1, 1, -1, -2], -9)]

theorem source334_checked : normalize (row ![0, 0, 1, 1, -1, -1] ![0, 0, 1, -1, 0, 0] (0, -3)) = source334 := by
  decide +kernel

theorem source334_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source334 (momentValues f) = 0 := by
  rw [← source334_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source335 : Sparse := [([0, -1, 0, -1, -1, 1, 2], 9), ([0, -1, 0, -1, -1, 2, 1], 9), ([0, 0, -1, -1, -1, 1, 2], -9), ([0, 0, -1, -1, -1, 2, 1], 9), ([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, 0, -2, -1, 1, 2], 9), ([0, 0, 0, -1, -1, 0, 2], 9), ([0, 0, 0, -1, 0, 0, 1], 9), ([0, 0, 0, 0, -2, 1, 1], 18), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, -1, -1, 1, 0], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, 0, -2, -1, 1, 1], 9), ([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 0, -1, -1, 1, 0], 9), ([1, -1, 0, -1, -1, 1, 2], 9), ([1, -1, 0, -1, -1, 2, 1], 9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, 0, -1, -1, -1, 2, 1], 9), ([1, 0, 0, -2, -1, 2, 1], 9), ([1, 0, 0, -1, -1, 0, 2], 9), ([1, 0, 0, -1, -1, 2, 0], -9), ([1, 0, 0, -1, 0, 1, 0], 9), ([1, 0, 0, 0, -2, 1, 1], 18), ([1, 0, 1, -2, -1, 1, 1], 9), ([1, 0, 1, -1, -1, 0, 1], 9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, 0, -1, -1, 1, 0], 9)]

theorem source335_checked : normalize (row ![0, 0, -1, -1, 1, 1] ![0, 0, -1, 1, 0, 0] (3, 3)) = source335 := by
  decide +kernel

theorem source335_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source335 (momentValues f) = 0 := by
  rw [← source335_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
