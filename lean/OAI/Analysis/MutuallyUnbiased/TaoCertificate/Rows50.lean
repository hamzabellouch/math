import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source400 : Sparse := [([0, -2, 0, 1, 1, 1, -1], 9), ([0, -2, 1, 0, 1, 1, -1], 9), ([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 0, -1, 2, 1, -1], 9), ([0, -1, 0, 0, 0, 2, -1], 18), ([0, -1, 0, 0, 2, 1, -2], 9), ([0, -1, 0, 1, 1, 1, -2], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, 1, 0, -1], 9), ([0, -1, 1, 0, 1, 1, -2], -9), ([0, 0, -1, 0, 1, 1, -1], 9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 0, 0, 0, 1, 0, -1], 9), ([0, 0, 0, 0, 1, 1, -2], 9), ([1, -2, 0, 0, 1, 1, 0], -9), ([1, -2, 0, 0, 2, 1, -1], 9), ([1, -2, 0, 1, 1, 1, -1], 9), ([1, -2, 1, 0, 1, 1, -1], 9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, -1, 0, 2, 1, -1], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, -1, 0, 0, 0, 2, -1], 18), ([1, -1, 0, 0, 1, 0, 0], 9), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, -1, 0, 1, 1, 1, -2], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, 0, -1, 0, 1, 1, -1], 9), ([1, 0, 0, 0, 1, 1, -2], 9)]

theorem source400_checked : normalize (row ![-1, 0, 0, 1, 1, -1] ![0, 0, 0, 1, -1, 0] (3, 3)) = source400 := by
  decide +kernel

theorem source400_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source400 (momentValues f) = 0 := by
  rw [← source400_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source401 : Sparse := [([0, 0, 0, 0, -1, 0, 1], 9), ([0, 0, 0, 1, -1, -1, 1], -9), ([0, 1, -1, 0, -1, -1, 2], -9), ([0, 1, -1, 0, -1, 0, 1], 9), ([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 0, 0, -2, -1, 2], 9), ([0, 1, 0, 0, -1, 0, 0], -9), ([0, 1, 0, 1, -2, -1, 1], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, 0, -2, -1, 1], -9), ([0, 2, 0, 0, -2, -1, 1], -9), ([0, 2, 0, 0, -1, -1, 0], 9), ([1, 0, 0, 0, -1, -1, 2], -9), ([1, 0, 1, 0, -1, -1, 1], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, 0, -1, -1, -1, 2], -9), ([1, 1, 0, -1, -1, 0, 1], -9), ([1, 1, 0, 0, -1, 0, 0], -9), ([1, 1, 0, 0, 0, -2, 1], -18), ([1, 1, 0, 1, -1, -1, 0], -9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, 0, -2, -1, 1], -9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 2, -1, 0, -1, -1, 1], -9), ([1, 2, 0, -1, -1, -1, 1], -9), ([1, 2, 0, 0, -2, -1, 1], -9), ([1, 2, 0, 0, -1, -1, 0], 9)]

theorem source401_checked : normalize (row ![1, 0, 0, -1, -1, 1] ![0, 0, 0, -1, 1, 0] (0, -3)) = source401 := by
  decide +kernel

theorem source401_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source401 (momentValues f) = 0 := by
  rw [← source401_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source402 : Sparse := [([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, 0, -2, -1, 1, 1, 1], 9), ([0, 0, -1, -2, 1, 1, 1], 9), ([0, 0, -1, -2, 2, 1, 0], 9), ([0, 0, -1, -1, 0, 2, 0], 18), ([0, 0, -1, -1, 2, 1, -1], 9), ([0, 0, -1, 0, 1, 1, -1], 9), ([0, 0, 0, -2, 1, 1, 0], 9), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 1, -2, -1, 1, 1, 0], 9), ([0, 1, -1, -2, 1, 1, 0], -9), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 2, 1, 0], 9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, 0, -2, -1, 1, 1, 1], 9), ([1, 0, -2, -1, 2, 1, 0], 9), ([1, 0, -2, 0, 1, 1, 0], -9), ([1, 0, -1, -2, 1, 1, 1], 9), ([1, 0, -1, -1, 0, 2, 0], 18), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, -1, 0, 1, 1, -1], 9), ([1, 0, 0, -2, 1, 1, 0], 9), ([1, 1, -2, -1, 1, 1, 0], 9), ([1, 1, -1, -1, 1, 1, -1], 9)]

theorem source402_checked : normalize (row ![0, -1, -1, 1, 1, 0] ![0, 0, 0, 1, -1, 0] (3, 3)) = source402 := by
  decide +kernel

theorem source402_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source402 (momentValues f) = 0 := by
  rw [← source402_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source403 : Sparse := [([0, -1, 1, 1, -1, 0, 0], 9), ([0, -1, 1, 2, -1, -1, 0], -9), ([0, 0, 0, 1, -1, -1, 1], -9), ([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 1, 0, -1, 0, 0], -9), ([0, 0, 1, 1, -2, -1, 1], 9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 0, 1, 2, -2, -1, 0], 9), ([0, 0, 2, 0, -1, -1, 0], 9), ([0, 0, 2, 1, -2, -1, 0], -9), ([0, 1, 1, 1, -2, -1, 0], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 2, 1, -1, -1, 0], -9), ([1, 0, 0, 2, -1, -1, 0], -9), ([1, 0, 1, 0, -1, -1, 1], -9), ([1, 0, 1, 0, -1, 0, 0], -9), ([1, 0, 1, 1, -1, 0, -1], -9), ([1, 0, 1, 1, 0, -2, 0], -18), ([1, 0, 1, 2, -1, -1, -1], -9), ([1, 0, 2, 0, -1, -1, 0], 9), ([1, 0, 2, 1, -2, -1, 0], -9), ([1, 0, 2, 1, -1, -1, -1], -9), ([1, 1, 0, 1, -1, -1, 0], -9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 1, 1, 1, -2, -1, 0], -9), ([1, 1, 1, 1, -1, -1, -1], 9)]

theorem source403_checked : normalize (row ![0, 1, 1, -1, -1, 0] ![0, 0, 0, -1, 1, 0] (0, -3)) = source403 := by
  decide +kernel

theorem source403_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source403 (momentValues f) = 0 := by
  rw [← source403_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source404 : Sparse := [([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, -1, 0, 2, 1, -1], 9), ([0, 0, -2, 0, 2, 1, -1], 9), ([0, 0, -2, 1, 1, 1, -1], -9), ([0, 0, -1, -1, 2, 1, -1], -9), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 0, -1, 0, 2, 1, -2], -9), ([0, 0, -1, 1, 1, 0, -1], 9), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 0, 0, 0, 1, 1, -2], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, 0, -2, 0, 1, 1, 0], -9), ([1, 0, -1, -1, 1, 1, 0], -9), ([1, 0, -1, -1, 2, 1, -1], -9), ([1, 0, -1, 0, 0, 2, -1], -18), ([1, 0, -1, 0, 2, 1, -2], -9), ([1, 0, -1, 1, 1, 1, -2], -9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 0, 0, 0, 1, 0, -1], -9), ([1, 0, 0, 0, 1, 1, -2], 9), ([1, 1, -2, 0, 1, 1, -1], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, -1, 0, 1, 1, -2], -9)]

theorem source404_checked : normalize (row ![0, -1, 0, 1, 1, -1] ![0, 0, 0, 1, -1, 0] (0, -3)) = source404 := by
  decide +kernel

theorem source404_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source404 (momentValues f) = 0 := by
  rw [← source404_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source405 : Sparse := [([0, -1, 1, 0, -1, -1, 2], 9), ([0, -1, 2, 0, -1, -1, 1], 9), ([0, 0, 0, 1, -1, -1, 1], 9), ([0, 0, 1, -1, -1, -1, 2], 9), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 0, 1, 0, 0, -2, 1], 18), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 0, 2, -1, -1, -1, 1], -9), ([0, 0, 2, 0, -2, -1, 1], 9), ([0, 0, 2, 0, -1, -1, 0], 9), ([0, 1, 0, 0, -1, -1, 1], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, 0, -2, -1, 1], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([1, -1, 1, 0, -1, -1, 2], 9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 2, 0, -1, -1, 1], 9), ([1, 0, 0, 0, -1, -1, 2], -9), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 0, 1, -1, -1, -1, 2], 9), ([1, 0, 1, 0, -2, -1, 2], 9), ([1, 0, 1, 0, 0, -2, 1], 18), ([1, 0, 1, 1, -2, -1, 1], 9), ([1, 0, 1, 1, -1, -1, 0], 9), ([1, 0, 2, 0, -1, -1, 0], 9), ([1, 1, 0, 0, -1, -1, 1], 9), ([1, 1, 1, -1, -1, -1, 1], 9)]

theorem source405_checked : normalize (row ![0, 1, 0, -1, -1, 1] ![0, 0, 0, -1, 1, 0] (3, 3)) = source405 := by
  decide +kernel

theorem source405_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source405 (momentValues f) = 0 := by
  rw [← source405_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source406 : Sparse := [([0, -1, 0, 0, 1, 1, -1], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, 0, -2, 1, 1, 0], 9), ([0, 0, 0, -2, 2, 1, -1], 9), ([0, 0, 0, -1, 0, 2, -1], 18), ([0, 0, 0, -1, 2, 1, -2], 9), ([0, 0, 0, 0, 1, 1, -2], 9), ([0, 0, 1, -2, 1, 1, -1], 9), ([0, 0, 1, -1, 1, 0, -1], 9), ([0, 0, 1, -1, 1, 1, -2], -9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, 0, -2, 1, 1, -1], -9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 1, 0, -1, 1, 1, -2], 9), ([1, -1, 0, -1, 1, 1, 0], -9), ([1, -1, 0, -1, 2, 1, -1], 9), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, 0, -1, -1, 1, 1, 0], 9), ([1, 0, -1, -1, 2, 1, -1], 9), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, 0, -2, 1, 1, 0], 9), ([1, 0, 0, -1, 0, 2, -1], 18), ([1, 0, 0, -1, 1, 0, 0], 9), ([1, 0, 0, 0, 1, 0, -1], 9), ([1, 0, 0, 0, 1, 1, -2], 9), ([1, 0, 1, -2, 1, 1, -1], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, 0, -1, 1, 1, -2], 9)]

theorem source406_checked : normalize (row ![0, 0, -1, 1, 1, -1] ![0, 0, 0, 1, -1, 0] (3, 3)) = source406 := by
  decide +kernel

theorem source406_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source406 (momentValues f) = 0 := by
  rw [← source406_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source407 : Sparse := [([0, -1, 0, 1, -1, 0, 1], 9), ([0, -1, 0, 2, -1, -1, 1], -9), ([0, 0, -1, 1, -1, -1, 2], -9), ([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, 0, 0, -1, 0, 1], -9), ([0, 0, 0, 1, -2, -1, 2], 9), ([0, 0, 0, 1, -1, 0, 0], -9), ([0, 0, 0, 2, -2, -1, 1], 9), ([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 1, 1, -2, -1, 1], -9), ([0, 1, 0, 1, -2, -1, 1], -9), ([0, 1, 0, 1, -1, -1, 0], 9), ([1, -1, 0, 1, -1, -1, 2], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, 0, -1, 2, -1, -1, 1], -9), ([1, 0, 0, 0, -1, -1, 2], -9), ([1, 0, 0, 0, -1, 0, 1], -9), ([1, 0, 0, 1, -1, 0, 0], -9), ([1, 0, 0, 1, 0, -2, 1], -18), ([1, 0, 0, 2, -1, -1, 0], -9), ([1, 0, 1, 0, -1, -1, 1], 9), ([1, 0, 1, 1, -2, -1, 1], -9), ([1, 0, 1, 1, -1, -1, 0], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, 0, 0, -1, -1, 1], -9), ([1, 1, 0, 1, -2, -1, 1], -9), ([1, 1, 0, 1, -1, -1, 0], 9)]

theorem source407_checked : normalize (row ![0, 0, 1, -1, -1, 1] ![0, 0, 0, -1, 1, 0] (0, -3)) = source407 := by
  decide +kernel

theorem source407_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source407 (momentValues f) = 0 := by
  rw [← source407_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
