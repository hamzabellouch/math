import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source464 : Sparse := [([0, -1, -1, 0, 2, -1, 1], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, 0, -2, 0, 2, -1, 1], 9), ([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, -1, -1, 2, -1, 1], 9), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 0, -1, 0, 2, -2, 1], -9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, 0, 0, 1, -2, 1], 9), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 1, -2, 0, 1, -1, 1], -9), ([0, 1, -1, 0, 1, -1, 0], 9), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, -1, 0, 2, -1, 1], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, 0, -2, 0, 1, 0, 1], -9), ([1, 0, -2, 1, 1, -1, 1], -9), ([1, 0, -1, 0, 0, -1, 2], -18), ([1, 0, -1, 0, 2, -2, 1], -9), ([1, 0, -1, 1, 1, -2, 1], -9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 0, 0, -1, 1, -1, 1], -9), ([1, 0, 0, 0, 1, -2, 1], 9), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, 0, 1, -2, 1], -9)]

theorem source464_checked : normalize (row ![0, -1, 0, 1, -1, 1] ![0, 0, 0, 1, 0, -1] (0, -3)) = source464 := by
  decide +kernel

theorem source464_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source464 (momentValues f) = 0 := by
  rw [← source464_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source465 : Sparse := [([0, -1, 1, 0, -1, 1, 0], 9), ([0, -1, 1, 0, -1, 2, -1], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 2, 0, -1, 1, -1], -9), ([0, 0, 0, 1, -1, 1, -1], 9), ([0, 0, 1, -1, -1, 2, -1], 9), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 0, 1, 0, 0, 1, -2], 18), ([0, 0, 1, 1, -2, 1, -1], 9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 0, 2, -1, -1, 1, -1], 9), ([0, 0, 2, 0, -2, 1, -1], 9), ([0, 0, 2, 0, -1, 0, -1], 9), ([0, 1, 0, 0, -1, 1, -1], 9), ([0, 1, 1, 0, -1, 0, -1], 9), ([1, -1, 1, 0, -1, 2, -1], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 0, 0, 0, -1, 2, -1], -9), ([1, 0, 0, 1, -1, 1, -1], 9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 0, 1, -1, -1, 2, -1], 9), ([1, 0, 1, 0, -2, 2, -1], 9), ([1, 0, 1, 0, 0, 1, -2], 18), ([1, 0, 2, -1, -1, 1, -1], 9), ([1, 0, 2, 0, -1, 0, -1], 9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, 0, -2, 1, -1], 9), ([1, 1, 1, 0, -1, 0, -1], 9)]

theorem source465_checked : normalize (row ![0, 1, 0, -1, 1, -1] ![0, 0, 0, -1, 0, 1] (3, 3)) = source465 := by
  decide +kernel

theorem source465_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source465 (momentValues f) = 0 := by
  rw [← source465_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source466 : Sparse := [([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 0, -1, 2, -1, 1], 9), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, 0, -1, -1, 1, 0, 1], 9), ([0, 0, -1, 0, 1, -1, 1], 9), ([0, 0, 0, -1, 0, -1, 2], 18), ([0, 0, 0, -1, 2, -2, 1], 9), ([0, 0, 0, 0, 1, -2, 1], 9), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 0, 1, -2, 1, -1, 1], 9), ([0, 0, 1, -1, 1, -2, 1], -9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 1, 0, -2, 1, -1, 1], 9), ([0, 1, 0, -1, 1, -2, 1], 9), ([1, -1, 0, -1, 1, 0, 1], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, -1, -1, 2, -1, 1], 9), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, 0, -2, 1, 0, 1], -9), ([1, 0, 0, -2, 2, -1, 1], 9), ([1, 0, 0, -1, 0, -1, 2], 18), ([1, 0, 0, -1, 1, 0, 0], 9), ([1, 0, 0, 0, 1, -2, 1], 9), ([1, 0, 1, -2, 1, -1, 1], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, 0, -2, 1, -1, 1], 9), ([1, 1, 0, -1, 1, -2, 1], 9), ([1, 1, 0, -1, 1, -1, 0], 9)]

theorem source466_checked : normalize (row ![0, 0, -1, 1, -1, 1] ![0, 0, 0, 1, 0, -1] (3, 3)) = source466 := by
  decide +kernel

theorem source466_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source466 (momentValues f) = 0 := by
  rw [← source466_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source467 : Sparse := [([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, -1, 1, -1, 2, -1], -9), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 0, 0, 1, -2, 2, -1], 9), ([0, 0, 0, 1, -1, 0, 0], -9), ([0, 0, 0, 2, -2, 1, -1], -9), ([0, 0, 0, 2, -1, 0, -1], 9), ([0, 0, 1, 1, -2, 1, -1], -9), ([0, 1, 0, 0, -1, 1, -1], -9), ([0, 1, 0, 1, -2, 1, -1], 9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 0, 1, -1, 2, -1], -9), ([1, -1, 0, 2, -1, 1, -1], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, 0, -1, 2, -1, 1, -1], -9), ([1, 0, 0, 0, -1, 2, -1], -9), ([1, 0, 0, 1, -1, 0, 0], -9), ([1, 0, 0, 1, 0, 1, -2], -18), ([1, 0, 0, 2, -2, 1, -1], -9), ([1, 0, 0, 2, -1, 0, -1], 9), ([1, 0, 1, 0, -1, 1, -1], -9), ([1, 0, 1, 1, -2, 1, -1], -9), ([1, 0, 1, 1, -1, 0, -1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, 0, 1, -1, 0, -1], -9)]

theorem source467_checked : normalize (row ![0, 0, 1, -1, 1, -1] ![0, 0, 0, -1, 0, 1] (0, -3)) = source467 := by
  decide +kernel

theorem source467_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source467 (momentValues f) = 0 := by
  rw [← source467_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source468 : Sparse := [([0, -2, -1, 0, 1, 1, 1], 9), ([0, -2, -1, 1, 0, 1, 1], 9), ([0, -1, -2, 0, 0, 2, 1], 9), ([0, -1, -2, 0, 1, 1, 1], 9), ([0, -1, -2, 1, 0, 1, 1], -9), ([0, -1, -1, 0, -1, 2, 1], 9), ([0, -1, -1, 0, 0, 0, 2], 18), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, 0, -1, 0, 1, 1], 9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, 0, -2, 0, 0, 1, 1], 9), ([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, -1, 0, 0, 1, 0], 9), ([1, -2, -1, 0, 0, 2, 1], 9), ([1, -2, -1, 0, 1, 1, 1], 9), ([1, -2, -1, 1, 0, 1, 1], 9), ([1, -2, 0, 0, 0, 1, 1], -9), ([1, -1, -2, 0, 1, 1, 1], 9), ([1, -1, -1, -1, 0, 2, 1], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, 0, 0, 0, 2], 18), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, 0, -2, 0, 0, 1, 1], 9), ([1, 0, -1, -1, 0, 1, 1], 9)]

theorem source468_checked : normalize (row ![-1, -1, 0, 0, 1, 1] ![0, 0, 0, 0, 1, -1] (3, 3)) = source468 := by
  decide +kernel

theorem source468_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source468 (momentValues f) = 0 := by
  rw [← source468_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source469 : Sparse := [([0, 0, 1, 0, 0, -1, 0], 9), ([0, 0, 1, 0, 1, -1, -1], -9), ([0, 1, 0, 0, 0, -1, 0], -9), ([0, 1, 1, -1, 0, -1, 0], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 1, 1, 0, 1, -2, -1], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, 0, -2, -1], -9), ([0, 1, 2, -1, 0, -1, -1], -9), ([0, 1, 2, 0, 0, -2, -1], 9), ([0, 2, 0, 0, 0, -1, -1], 9), ([0, 2, 1, 0, 0, -2, -1], -9), ([1, 0, 1, 1, 0, -1, -1], -9), ([1, 0, 2, 0, 0, -1, -1], -9), ([1, 1, 0, 0, 0, -1, 0], -9), ([1, 1, 0, 0, 1, -1, -1], -9), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 1, 1, 0, 0, 0, -2], -18), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, 0, -2, -1], -9), ([1, 1, 2, 0, -1, -1, -1], -9), ([1, 2, 0, 0, 0, -1, -1], 9), ([1, 2, 1, -1, 0, -1, -1], -9), ([1, 2, 1, 0, -1, -1, -1], -9), ([1, 2, 1, 0, 0, -2, -1], -9)]

theorem source469_checked : normalize (row ![1, 1, 0, 0, -1, -1] ![0, 0, 0, 0, -1, 1] (0, -3)) = source469 := by
  decide +kernel

theorem source469_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source469 (momentValues f) = 0 := by
  rw [← source469_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source470 : Sparse := [([0, -2, 0, -1, 0, 2, 1], 9), ([0, -2, 1, -1, 0, 1, 1], -9), ([0, -1, -1, -1, 0, 2, 1], -9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, 0, -2, 0, 2, 1], 9), ([0, -1, 0, -2, 1, 1, 1], -9), ([0, -1, 0, -1, -1, 2, 1], -9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 0, 0, 0, 1, 0], -9), ([0, -1, 1, -1, 0, 1, 0], 9), ([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 0, -1, 0, 1, 0], -9), ([1, -2, 0, -1, 1, 1, 1], -9), ([1, -2, 0, 0, 0, 1, 1], -9), ([1, -1, -1, -1, 0, 2, 1], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, 0, 0, 1, 1], 9), ([1, -1, 0, -1, -1, 2, 1], -9), ([1, -1, 0, -1, 0, 0, 2], -18), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, -1, 0, 0, 0, 1, 0], -9), ([1, -1, 1, -2, 0, 1, 1], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, 0, -1, -1, 0, 1, 1], -9), ([1, 0, 0, -2, 0, 1, 1], -9), ([1, 0, 0, -1, -1, 1, 1], 9), ([1, 0, 0, -1, 0, 1, 0], -9)]

theorem source470_checked : normalize (row ![-1, 0, -1, 0, 1, 1] ![0, 0, 0, 0, 1, -1] (0, -3)) = source470 := by
  decide +kernel

theorem source470_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source470 (momentValues f) = 0 := by
  rw [← source470_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source471 : Sparse := [([0, 0, 0, 2, 0, -1, -1], 9), ([0, 0, 1, 1, 0, -1, -1], 9), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, -1, 2, 0, -1, -1], 9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 1, 0, 1, -1, -1, 0], 9), ([0, 1, 0, 1, 0, 0, -2], 18), ([0, 1, 0, 2, -1, -1, -1], -9), ([0, 1, 0, 2, 0, -2, -1], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 2, -1, 1, 0, -1, -1], -9), ([0, 2, 0, 0, 0, -1, -1], 9), ([0, 2, 0, 1, -1, -1, -1], 9), ([0, 2, 0, 1, 0, -2, -1], 9), ([1, 0, 0, 1, 0, -1, 0], 9), ([1, 0, 0, 1, 1, -1, -1], -9), ([1, 0, 0, 2, 0, -1, -1], 9), ([1, 0, 1, 1, 0, -1, -1], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 2, 0, -1, -1], 9), ([1, 1, 0, 0, 0, -1, 0], 9), ([1, 1, 0, 0, 1, -1, -1], 9), ([1, 1, 0, 1, 0, 0, -2], 18), ([1, 1, 0, 1, 1, -2, -1], 9), ([1, 1, 1, 0, 0, -1, -1], -9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, 0, -2, -1], 9), ([1, 2, 0, 0, 0, -1, -1], 9), ([1, 2, 0, 1, -1, -1, -1], 9)]

theorem source471_checked : normalize (row ![1, 0, 1, 0, -1, -1] ![0, 0, 0, 0, -1, 1] (3, 3)) = source471 := by
  decide +kernel

theorem source471_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source471 (momentValues f) = 0 := by
  rw [← source471_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
