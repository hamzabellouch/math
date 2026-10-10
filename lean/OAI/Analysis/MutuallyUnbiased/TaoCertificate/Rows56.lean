import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source448 : Sparse := [([0, -2, 0, 1, 0, 0, 1], 9), ([0, -2, 0, 1, 1, -1, 1], -9), ([0, -2, 0, 2, 0, -1, 1], 9), ([0, -2, 1, 1, 0, -1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 2, 0, -1, 1], 9), ([0, -1, 0, 0, 0, -1, 2], 18), ([0, -1, 0, 1, -1, 0, 1], 9), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 1, 1, -2, 1], 9), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, -1, 1, 1, 0, -2, 1], 9), ([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, 0, 1, -1, -1, 1], 9), ([1, -2, 0, 1, 0, 0, 1], 9), ([1, -2, 1, 1, 0, -1, 1], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, 0, 0, 0, -1, 2], 18), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 0, 1, 1, -2, 1], 9), ([1, -1, 0, 2, -1, -1, 1], 9), ([1, -1, 0, 2, 0, -2, 1], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, 0, -2, 1], 9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 0, 0, 1, 0, -2, 1], -9), ([1, 0, 0, 1, 0, -1, 0], 9)]

theorem source448_checked : normalize (row ![-1, 0, 1, 0, -1, 1] ![0, 0, 1, 0, 0, -1] (3, 3)) = source448 := by
  decide +kernel

theorem source448_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source448 (momentValues f) = 0 := by
  rw [← source448_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source449 : Sparse := [([0, 0, 0, -1, 0, 1, 0], -9), ([0, 0, 0, -1, 0, 2, -1], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, 0, -2, 0, 2, -1], -9), ([0, 1, 0, -2, 1, 1, -1], -9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 1, 0, -1, 0, 0, 0], 9), ([0, 1, 1, -2, 0, 1, -1], 9), ([0, 1, 1, -1, 0, 0, -1], -9), ([0, 2, 0, -2, 0, 1, -1], 9), ([0, 2, 0, -1, -1, 1, -1], -9), ([1, 0, 0, -1, 0, 1, 0], -9), ([1, 0, 0, -1, 0, 2, -1], 9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 0, 1, -1, 0, 1, -1], -9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, -1, -1, 0, 2, -1], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, 0, -2, 0, 2, -1], -9), ([1, 1, 0, -2, 1, 1, -1], -9), ([1, 1, 0, -1, -1, 2, -1], -9), ([1, 1, 0, -1, 1, 0, -1], -9), ([1, 1, 0, 0, 0, 1, -2], -18), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 2, -1, -1, 0, 1, -1], -9), ([1, 2, 0, -1, 0, 0, -1], -9)]

theorem source449_checked : normalize (row ![1, 0, -1, 0, 1, -1] ![0, 0, -1, 0, 0, 1] (0, -3)) = source449 := by
  decide +kernel

theorem source449_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source449 (momentValues f) = 0 := by
  rw [← source449_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source450 : Sparse := [([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, -1, 2, -1, 0, 1], 9), ([0, -1, 0, 1, -1, 0, 1], 9), ([0, 0, -2, 1, -1, 1, 1], -9), ([0, 0, -2, 1, 0, 0, 1], 9), ([0, 0, -2, 2, -1, 0, 1], 9), ([0, 0, -1, 0, -1, 0, 2], 18), ([0, 0, -1, 1, -2, 1, 1], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, -1, 1, 0, 0, 0], 9), ([0, 0, 0, 1, -1, -1, 1], 9), ([0, 1, -2, 1, -1, 0, 1], 9), ([0, 1, -1, 1, -2, 0, 1], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, 0, -2, 1, 0, 0, 1], 9), ([1, 0, -1, 0, -1, 0, 2], 18), ([1, 0, -1, 1, -2, 1, 1], 9), ([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, -1, 2, -2, 0, 1], 9), ([1, 0, -1, 2, -1, -1, 1], 9), ([1, 0, 0, 1, -2, 0, 1], -9), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 1, -2, 1, -1, 0, 1], 9), ([1, 1, -1, 1, -2, 0, 1], 9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, -1, 0, 0], 9)]

theorem source450_checked : normalize (row ![0, -1, 1, -1, 0, 1] ![0, 0, 1, 0, 0, -1] (3, 3)) = source450 := by
  decide +kernel

theorem source450_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source450 (momentValues f) = 0 := by
  rw [← source450_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source451 : Sparse := [([0, -1, 1, -1, 1, 0, 0], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 0, 0, -1, 2, 0, -1], 9), ([0, 0, 1, -2, 1, 1, -1], -9), ([0, 0, 1, -2, 2, 0, -1], -9), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 0, 2, -2, 1, 0, -1], 9), ([0, 0, 2, -1, 1, -1, -1], -9), ([0, 1, 1, -2, 1, 0, -1], 9), ([0, 1, 1, -1, 0, 0, -1], -9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, -1, 2, 0, -1], -9), ([1, -1, 2, -1, 1, 0, -1], -9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 0, 0, -1, 2, 0, -1], 9), ([1, 0, 1, -2, 1, 1, -1], -9), ([1, 0, 1, -2, 2, 0, -1], -9), ([1, 0, 1, -1, 0, 1, -1], -9), ([1, 0, 1, -1, 2, -1, -1], -9), ([1, 0, 1, 0, 1, 0, -2], -18), ([1, 0, 2, -1, 0, 0, -1], -9), ([1, 1, 0, -1, 1, 0, -1], -9), ([1, 1, 1, -1, 1, -1, -1], -9)]

theorem source451_checked : normalize (row ![0, 1, -1, 1, 0, -1] ![0, 0, -1, 0, 0, 1] (0, -3)) = source451 := by
  decide +kernel

theorem source451_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source451 (momentValues f) = 0 := by
  rw [← source451_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source452 : Sparse := [([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 2, 0, -1, 1], -9), ([0, 0, -2, 1, 0, 0, 1], 9), ([0, 0, -2, 2, 0, -1, 1], -9), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, -1, 2, -1, -1, 1], 9), ([0, 0, -1, 2, 0, -2, 1], 9), ([0, 0, 0, 1, -1, -1, 1], -9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 1, -1, 1, 0, -2, 1], -9), ([0, 1, -1, 1, 0, -1, 0], 9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 2, 0, -1, 1], -9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, 0, -2, 1, 0, 0, 1], 9), ([1, 0, -2, 1, 1, -1, 1], -9), ([1, 0, -2, 2, 0, -1, 1], -9), ([1, 0, -1, 0, 0, -1, 2], -18), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, -2, 1], -9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 0, 0, 1, 0, -2, 1], -9), ([1, 1, -2, 1, 0, -1, 1], -9), ([1, 1, -1, 1, -1, -1, 1], -9)]

theorem source452_checked : normalize (row ![0, -1, 1, 0, -1, 1] ![0, 0, 1, 0, 0, -1] (0, -3)) = source452 := by
  decide +kernel

theorem source452_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source452 (momentValues f) = 0 := by
  rw [← source452_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source453 : Sparse := [([0, -1, 1, -1, 0, 1, 0], 9), ([0, -1, 1, -1, 0, 2, -1], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 2, -1, 0, 1, -1], 9), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 0, 0, -1, 0, 2, -1], 9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 0, 1, -2, 0, 2, -1], 9), ([0, 0, 1, -2, 1, 1, -1], 9), ([0, 0, 1, -1, -1, 2, -1], 9), ([0, 0, 1, -1, 1, 0, -1], 9), ([0, 0, 1, 0, 0, 1, -2], 18), ([0, 0, 2, -1, -1, 1, -1], 9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 1, 1, -1, 0, 0, -1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 2, -1, 0, 1, -1], 9), ([1, 0, 0, -1, 0, 2, -1], 9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 0, 1, -1, -1, 2, -1], 9), ([1, 0, 1, -1, 0, 0, 0], 9), ([1, 0, 1, -1, 1, 0, -1], 9), ([1, 0, 1, 0, 0, 1, -2], 18), ([1, 0, 2, -2, 0, 1, -1], 9), ([1, 0, 2, -1, -1, 1, -1], 9), ([1, 0, 2, -1, 0, 0, -1], -9), ([1, 1, 0, -1, 0, 1, -1], 9), ([1, 1, 1, -2, 0, 1, -1], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 0, 0, -1], 9)]

theorem source453_checked : normalize (row ![0, 1, -1, 0, 1, -1] ![0, 0, -1, 0, 0, 1] (3, 3)) = source453 := by
  decide +kernel

theorem source453_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source453 (momentValues f) = 0 := by
  rw [← source453_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source454 : Sparse := [([0, -1, 0, 1, 0, -1, 1], 9), ([0, -1, 0, 2, -1, -1, 1], -9), ([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, -1, 2, -1, -1, 1], -9), ([0, 0, 0, 1, -1, 0, 0], -9), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 0, 0, 2, -2, -1, 1], 9), ([0, 0, 0, 2, -1, -2, 1], 9), ([0, 0, 1, 1, -2, -1, 1], -9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 1, 0, 1, -1, -2, 1], -9), ([0, 1, 0, 1, -1, -1, 0], 9), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, -1, 0, 2, -1, -1, 1], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, -1, 2, -1, -1, 1], -9), ([1, 0, 0, 0, -1, -1, 2], -18), ([1, 0, 0, 1, -2, 0, 1], -9), ([1, 0, 0, 1, -1, 0, 0], -9), ([1, 0, 0, 1, 0, -2, 1], -9), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 0, 1, 1, -1, -2, 1], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, 0, 1, -2, -1, 1], -9)]

theorem source454_checked : normalize (row ![0, 0, 1, -1, -1, 1] ![0, 0, 1, 0, 0, -1] (0, -3)) = source454 := by
  decide +kernel

theorem source454_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source454 (momentValues f) = 0 := by
  rw [← source454_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source455 : Sparse := [([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 0, -1, 1, 2, -1], -9), ([0, -1, 0, -1, 2, 1, -1], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, -1, -1, 1, 2, -1], 9), ([0, 0, -1, -1, 2, 1, -1], -9), ([0, 0, 0, -2, 1, 2, -1], 9), ([0, 0, 0, -2, 2, 1, -1], 9), ([0, 0, 0, -1, 0, 2, -1], 9), ([0, 0, 0, -1, 2, 0, -1], 9), ([0, 0, 0, 0, 1, 1, -2], 18), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, 0, -1, 1, 0, -1], 9), ([1, -1, 0, -1, 2, 1, -1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, 0, -1, -1, 1, 2, -1], 9), ([1, 0, 0, -1, 0, 1, 0], 9), ([1, 0, 0, -1, 0, 2, -1], 9), ([1, 0, 0, -1, 1, 0, 0], 9), ([1, 0, 0, -1, 2, 0, -1], 9), ([1, 0, 0, 0, 1, 1, -2], 18), ([1, 0, 1, -2, 1, 1, -1], 9), ([1, 0, 1, -1, 0, 1, -1], 9), ([1, 0, 1, -1, 1, 0, -1], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, 0, -2, 1, 1, -1], 9), ([1, 1, 0, -1, 0, 1, -1], -9), ([1, 1, 0, -1, 1, 0, -1], 9)]

theorem source455_checked : normalize (row ![0, 0, -1, 1, 1, -1] ![0, 0, -1, 0, 0, 1] (3, 3)) = source455 := by
  decide +kernel

theorem source455_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source455 (momentValues f) = 0 := by
  rw [← source455_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
