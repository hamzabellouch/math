import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source432 : Sparse := [([0, -2, 1, -1, 0, 1, 1], -9), ([0, -2, 2, -1, 0, 0, 1], 9), ([0, -1, 1, -1, 0, 1, 0], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 1, 0, 0, 0, 0], 9), ([0, -1, 2, -2, 0, 0, 1], -9), ([0, -1, 2, -1, -1, 0, 1], 9), ([0, -1, 2, -1, 0, -1, 1], -9), ([0, 0, 1, -2, 0, 0, 1], 9), ([0, 0, 1, -1, 0, 0, 0], -9), ([1, -2, 1, -1, 1, 0, 1], -9), ([1, -2, 1, 0, 0, 0, 1], -9), ([1, -1, 0, -1, 0, 0, 2], -18), ([1, -1, 1, -2, 0, 1, 1], -9), ([1, -1, 1, -2, 1, 0, 1], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 2, -2, 0, 0, 1], -9), ([1, -1, 2, -1, 0, -1, 1], -9), ([1, 0, 1, -2, 0, 0, 1], 9), ([1, 0, 1, -1, -1, 0, 1], -9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 0, 1, -1, 0, 0, 0], -9)]

theorem source432_checked : normalize (row ![-1, 1, -1, 0, 0, 1] ![0, 1, 0, 0, 0, -1] (0, -3)) = source432 := by
  decide +kernel

theorem source432_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source432 (momentValues f) = 0 := by
  rw [← source432_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source433 : Sparse := [([0, 0, -1, 1, 0, 1, -1], 9), ([0, 0, -1, 1, 1, 0, -1], 9), ([0, 1, -2, 1, 1, 0, -1], 9), ([0, 1, -1, 0, 0, 0, 0], 9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, -1, 2, -1, 0, -1], 9), ([0, 1, -1, 2, 0, -1, -1], 9), ([0, 1, 0, 1, 0, 0, -2], 18), ([0, 2, -2, 1, 0, 0, -1], 9), ([0, 2, -1, 0, 0, 0, -1], 9), ([0, 2, -1, 1, -1, 0, -1], 9), ([0, 2, -1, 1, 0, -1, -1], -9), ([1, 0, -1, 1, 0, 0, 0], 9), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, -1, 2, 0, 0, -1], -9), ([1, 1, -2, 1, 0, 1, -1], 9), ([1, 1, -2, 2, 0, 0, -1], 9), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 2, -1, 0, -1], 9), ([1, 1, -1, 2, 0, -1, -1], 9), ([1, 1, 0, 1, 0, 0, -2], 18), ([1, 2, -1, 0, 0, 0, -1], 9), ([1, 2, -1, 1, -1, 0, -1], 9)]

theorem source433_checked : normalize (row ![1, -1, 1, 0, 0, -1] ![0, -1, 0, 0, 0, 1] (3, 3)) = source433 := by
  decide +kernel

theorem source433_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source433 (momentValues f) = 0 := by
  rw [← source433_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source434 : Sparse := [([0, -2, 1, 0, -1, 1, 1], -9), ([0, -2, 2, 0, -1, 0, 1], 9), ([0, -1, 1, 0, -1, 1, 0], 9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, -1, 1, 0, 0, 0, 0], -9), ([0, -1, 1, 1, -2, 0, 1], -9), ([0, -1, 1, 1, -1, 0, 0], 9), ([0, -1, 2, -1, -1, 0, 1], -9), ([0, -1, 2, 0, -2, 0, 1], 9), ([0, -1, 2, 0, -1, -1, 1], -9), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, 0, -1, 0, 0], -9), ([1, -2, 1, 0, 0, 0, 1], -9), ([1, -2, 1, 1, -1, 0, 1], -9), ([1, -1, 0, 0, -1, 0, 2], -18), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, 0, -2, 1, 1], -9), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 0, 0, 0, 0], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 2, -1, -1, 0, 1], -9), ([1, -1, 2, 0, -1, -1, 1], -9), ([1, 0, 1, -1, -1, 0, 1], 9), ([1, 0, 1, 0, -2, 0, 1], -9), ([1, 0, 1, 0, -1, -1, 1], -9), ([1, 0, 1, 0, -1, 0, 0], -9)]

theorem source434_checked : normalize (row ![-1, 1, 0, -1, 0, 1] ![0, 1, 0, 0, 0, -1] (0, -3)) = source434 := by
  decide +kernel

theorem source434_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source434 (momentValues f) = 0 := by
  rw [← source434_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source435 : Sparse := [([0, 0, -1, 0, 1, 1, -1], 9), ([0, 0, -1, 0, 2, 0, -1], 9), ([0, 1, -2, 0, 2, 0, -1], 9), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, -1, 2, 0, -1], -9), ([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, -1, 0, 2, -1, -1], 9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, 0, 1, 0, -2], 18), ([0, 2, -2, 0, 1, 0, -1], 9), ([0, 2, -1, -1, 1, 0, -1], 9), ([0, 2, -1, 0, 0, 0, -1], 9), ([0, 2, -1, 0, 1, -1, -1], -9), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, -1, 0, 1, 1, -1], 9), ([1, 0, -1, 0, 2, 0, -1], 9), ([1, 0, -1, 1, 1, 0, -1], -9), ([1, 1, -2, 0, 1, 1, -1], 9), ([1, 1, -2, 1, 1, 0, -1], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, 0, 0, 0], 9), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 0, 2, -1, -1], 9), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, 0, 1, 0, -2], 18), ([1, 2, -1, -1, 1, 0, -1], 9), ([1, 2, -1, 0, 0, 0, -1], 9)]

theorem source435_checked : normalize (row ![1, -1, 0, 1, 0, -1] ![0, -1, 0, 0, 0, 1] (3, 3)) = source435 := by
  decide +kernel

theorem source435_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source435 (momentValues f) = 0 := by
  rw [← source435_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source436 : Sparse := [([0, -2, 1, 0, 1, -1, 1], 9), ([0, -2, 1, 1, 0, -1, 1], 9), ([0, -1, 0, 0, 0, -1, 2], 18), ([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 0, 1, -2, 1], -9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, -1, 1, 1, 0, -2, 1], 9), ([0, -1, 2, -1, 0, -1, 1], 9), ([0, -1, 2, 0, 0, -2, 1], 9), ([0, 0, 1, -1, 0, -1, 1], -9), ([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 1, 0, 0, -2, 1], 9), ([0, 0, 1, 0, 0, -1, 0], 9), ([1, -2, 1, 0, 0, 0, 1], -9), ([1, -2, 1, 0, 1, -1, 1], 9), ([1, -2, 1, 1, 0, -1, 1], 9), ([1, -2, 2, 0, 0, -1, 1], 9), ([1, -1, 0, 0, 0, -1, 2], 18), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 1, 0, 0, 0, 0], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, 0, -2, 1], 9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, -1, 2, 0, -1, -1, 1], 9), ([1, 0, 1, 0, -1, -1, 1], 9), ([1, 0, 1, 0, 0, -2, 1], 9)]

theorem source436_checked : normalize (row ![-1, 1, 0, 0, -1, 1] ![0, 1, 0, 0, 0, -1] (3, 3)) = source436 := by
  decide +kernel

theorem source436_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source436 (momentValues f) = 0 := by
  rw [← source436_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source437 : Sparse := [([0, 0, -1, 0, 0, 1, 0], 9), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 1, -2, 0, 0, 2, -1], 9), ([0, 1, -2, 0, 1, 1, -1], -9), ([0, 1, -2, 1, 0, 1, -1], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, -1, 1, 0], 9), ([0, 1, -1, 0, -1, 2, -1], -9), ([0, 1, -1, 0, 0, 0, 0], -9), ([0, 2, -2, 0, 0, 1, -1], -9), ([0, 2, -1, 0, 0, 0, -1], 9), ([1, 0, -1, 0, 0, 2, -1], -9), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 1, -2, 0, 1, 1, -1], -9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, -1, -1, 0, 2, -1], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, 0, 0, 0], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, 0, 0, 0, 1, -2], -18), ([1, 2, -2, 0, 0, 1, -1], -9), ([1, 2, -1, -1, 0, 1, -1], -9), ([1, 2, -1, 0, -1, 1, -1], -9), ([1, 2, -1, 0, 0, 0, -1], 9)]

theorem source437_checked : normalize (row ![1, -1, 0, 0, 1, -1] ![0, -1, 0, 0, 0, 1] (0, -3)) = source437 := by
  decide +kernel

theorem source437_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source437 (momentValues f) = 0 := by
  rw [← source437_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source438 : Sparse := [([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, 0, 0, -1, -1, 0, 2], 18), ([0, 0, 1, -2, -1, 1, 1], 9), ([0, 0, 1, -2, 0, 0, 1], 9), ([0, 0, 1, -1, -2, 1, 1], 9), ([0, 0, 1, -1, 0, -1, 1], -9), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 2, -2, -1, 0, 1], 9), ([0, 0, 2, -1, -1, -1, 1], 9), ([0, 1, 1, -2, -1, 0, 1], -9), ([0, 1, 1, -1, -2, 0, 1], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, -1, 0, 0], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 2, -1, -1, 0, 1], 9), ([1, 0, 0, -1, -1, 0, 2], 18), ([1, 0, 1, -2, -1, 1, 1], 9), ([1, 0, 1, -2, 0, 0, 1], 9), ([1, 0, 1, -1, -2, 1, 1], 9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 0, 1, 0, -2, 0, 1], -9), ([1, 0, 1, 0, -1, -1, 1], 9), ([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 2, -1, -2, 0, 1], 9), ([1, 1, 1, -1, -2, 0, 1], 9), ([1, 1, 1, -1, -1, -1, 1], 9)]

theorem source438_checked : normalize (row ![0, 1, -1, -1, 0, 1] ![0, 1, 0, 0, 0, -1] (3, 3)) = source438 := by
  decide +kernel

theorem source438_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source438 (momentValues f) = 0 := by
  rw [← source438_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source439 : Sparse := [([0, -1, -1, 1, 1, 0, 0], 9), ([0, -1, -1, 2, 1, 0, -1], -9), ([0, 0, -2, 1, 1, 1, -1], 9), ([0, 0, -2, 1, 2, 0, -1], -9), ([0, 0, -2, 2, 1, 0, -1], 9), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 2, 0, -1], 9), ([0, 0, -1, 1, 0, 0, 0], 9), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 1, -2, 1, 1, 0, -1], -9), ([0, 1, -1, 1, 1, -1, -1], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 1, 2, 0, -1], -9), ([1, 0, -2, 1, 2, 0, -1], -9), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, -1, 0, 2, 0, -1], 9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 0, -1, 1, 2, -1, -1], -9), ([1, 0, -1, 2, 0, 0, -1], -9), ([1, 0, -1, 2, 1, -1, -1], -9), ([1, 0, 0, 1, 1, 0, -2], -18), ([1, 1, -2, 1, 1, 0, -1], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, -1, 1, 1, -1, -1], 9)]

theorem source439_checked : normalize (row ![0, -1, 1, 1, 0, -1] ![0, -1, 0, 0, 0, 1] (0, -3)) = source439 := by
  decide +kernel

theorem source439_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source439 (momentValues f) = 0 := by
  rw [← source439_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
