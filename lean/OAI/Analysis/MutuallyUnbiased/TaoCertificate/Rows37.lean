import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source296 : Sparse := [([0, -1, -1, 1, 0, -1, 2], 9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, 0, 1, 0, -1, 1], 9), ([0, 0, -2, 1, 0, -1, 2], 9), ([0, 0, -2, 1, 0, 0, 1], 9), ([0, 0, -2, 1, 1, -1, 1], -9), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 0, 1, -1, 1], 9), ([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, -1, 1, 1, -2, 1], 9), ([0, 0, -1, 2, 0, -1, 0], 18), ([0, 0, 0, 1, -1, -1, 1], 9), ([0, 1, -2, 1, 0, -1, 1], 9), ([0, 1, -1, 1, 0, -2, 1], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, 0, -2, 1, 0, 0, 1], 9), ([1, 0, -1, 1, -1, -1, 2], 9), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, -1, 1, 0, -2, 2], 9), ([1, 0, -1, 1, 1, -2, 1], 9), ([1, 0, -1, 2, 0, -1, 0], 18), ([1, 0, 0, 0, 0, -1, 1], 9), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 0, 0, 1, 0, -2, 1], -9), ([1, 1, -2, 1, 0, -1, 1], 9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, 0, -2, 1], 9)]

theorem source296_checked : normalize (row ![0, -1, 1, 0, -1, 1] ![0, 0, -1, 0, 0, 1] (3, 3)) = source296 := by
  decide +kernel

theorem source296_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source296 (momentValues f) = 0 := by
  rw [← source296_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source297 : Sparse := [([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, 0, 1, -1], -9), ([0, 0, 0, -1, 0, 2, -1], 9), ([0, 0, 0, 0, 0, 1, -1], -9), ([0, 0, 1, -1, 0, 2, -2], -9), ([0, 0, 1, -1, 1, 1, -2], -9), ([0, 0, 1, 0, -1, 1, -1], 9), ([0, 0, 1, 0, 0, 0, -1], 9), ([0, 0, 2, -1, -1, 1, -1], -9), ([0, 0, 2, -1, 0, 1, -2], 9), ([0, 1, 1, -1, 0, 0, -1], -9), ([0, 1, 1, -1, 0, 1, -2], 9), ([1, -1, 1, -1, 0, 2, -1], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 2, -1, 0, 1, -1], -9), ([1, 0, 0, -1, 0, 2, -1], 9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 0, 0, 0, 0, 1, -1], -9), ([1, 0, 1, -2, 0, 1, 0], -18), ([1, 0, 1, -1, -1, 2, -1], -9), ([1, 0, 1, -1, 0, 2, -2], -9), ([1, 0, 1, -1, 1, 0, -1], -9), ([1, 0, 1, -1, 1, 1, -2], -9), ([1, 0, 2, -1, 0, 0, -1], -9), ([1, 1, 0, -1, 0, 1, -1], -9), ([1, 1, 1, -1, -1, 1, -1], -9)]

theorem source297_checked : normalize (row ![0, 1, -1, 0, 1, -1] ![0, 0, 1, 0, 0, -1] (0, -3)) = source297 := by
  decide +kernel

theorem source297_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source297 (momentValues f) = 0 := by
  rw [← source297_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source298 : Sparse := [([0, -1, 0, 1, -1, -1, 2], -9), ([0, -1, 0, 1, -1, 0, 1], 9), ([0, 0, -1, 1, -1, -1, 2], -9), ([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, 0, 0, -1, 0, 1], -9), ([0, 0, 0, 0, 0, -1, 1], -9), ([0, 0, 0, 1, -2, -1, 2], 9), ([0, 0, 0, 1, -1, -2, 2], 9), ([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 1, 1, -1, -2, 1], -9), ([0, 1, 0, 0, -1, -1, 1], 9), ([0, 1, 0, 1, -2, -1, 1], -9), ([1, -1, 0, 1, -1, -1, 2], -9), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, 0, -1, 1, -1, -1, 2], -9), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, 0, 0, -1, 0, 1], -9), ([1, 0, 0, 0, 0, -1, 1], -9), ([1, 0, 0, 1, -2, 0, 1], -9), ([1, 0, 0, 1, 0, -2, 1], -9), ([1, 0, 0, 2, -1, -1, 0], -18), ([1, 0, 1, 1, -2, -1, 1], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, 0, 1, -1, -2, 1], -9)]

theorem source298_checked : normalize (row ![0, 0, 1, -1, -1, 1] ![0, 0, -1, 0, 0, 1] (0, -3)) = source298 := by
  decide +kernel

theorem source298_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source298 (momentValues f) = 0 := by
  rw [← source298_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source299 : Sparse := [([0, -1, 0, -1, 1, 2, -1], 9), ([0, -1, 0, -1, 2, 1, -1], -9), ([0, -1, 0, 0, 1, 1, -1], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, 0, -1, -1, 1, 2, -1], -9), ([0, 0, -1, -1, 2, 1, -1], 9), ([0, 0, -1, 0, 1, 1, -1], 9), ([0, 0, 0, -2, 1, 1, 0], 18), ([0, 0, 0, -1, 0, 2, -1], 9), ([0, 0, 0, -1, 1, 2, -2], 9), ([0, 0, 0, -1, 2, 0, -1], 9), ([0, 0, 0, -1, 2, 1, -2], 9), ([0, 0, 1, -1, 1, 0, -1], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, 0, -1, 0, 1, -1], 9), ([1, -1, 0, -1, 1, 2, -1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, 0, -1, -1, 2, 1, -1], 9), ([1, 0, 0, -2, 1, 1, 0], 18), ([1, 0, 0, -1, 0, 2, -1], 9), ([1, 0, 0, -1, 2, 0, -1], 9), ([1, 0, 0, 0, 0, 1, -1], 9), ([1, 0, 0, 0, 1, 0, -1], 9), ([1, 0, 1, -1, 0, 1, -1], -9), ([1, 0, 1, -1, 1, 0, -1], 9), ([1, 0, 1, -1, 1, 1, -2], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, 0, -1, 0, 1, -1], 9), ([1, 1, 0, -1, 1, 0, -1], -9), ([1, 1, 0, -1, 1, 1, -2], 9)]

theorem source299_checked : normalize (row ![0, 0, -1, 1, 1, -1] ![0, 0, 1, 0, 0, -1] (3, 3)) = source299 := by
  decide +kernel

theorem source299_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source299 (momentValues f) = 0 := by
  rw [← source299_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source300 : Sparse := [([0, 1, -2, 0, 1, 0, 0], 9), ([0, 1, -1, -2, 1, 0, 1], -9), ([0, 1, -1, -1, 0, 0, 1], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, 0, 0, 0], -9), ([0, 1, 0, -1, 0, 0, 0], 9), ([0, 1, 0, -1, 1, -1, 0], -9), ([0, 2, -2, -1, 1, 0, 0], -9), ([0, 2, -1, -2, 1, 0, 0], 9), ([0, 2, -1, -1, 1, -1, 0], 9), ([0, 2, -1, -1, 1, 0, -1], -9), ([1, 0, -1, -1, 2, 0, 0], -18), ([1, 1, -2, -1, 1, 0, 1], -9), ([1, 1, -2, -1, 1, 1, 0], -9), ([1, 1, -2, 0, 1, 0, 0], 9), ([1, 1, -1, -2, 1, 1, 0], -9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, 0, 0, 0], -9), ([1, 1, -1, 0, 1, -1, 0], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, 0, -2, 1, 0, 0], -9), ([1, 1, 0, -1, 1, 0, -1], -9), ([1, 2, -2, -1, 1, 0, 0], -9), ([1, 2, -1, -1, 1, 0, -1], -9)]

theorem source300_checked : normalize (row ![1, -1, -1, 1, 0, 0] ![1, 0, 0, -1, 0, 0] (0, -3)) = source300 := by
  decide +kernel

theorem source300_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source300 (momentValues f) = 0 := by
  rw [← source300_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source301 : Sparse := [([0, -2, 1, 1, -1, 1, 0], 9), ([0, -2, 1, 2, -1, 0, 0], 9), ([0, -1, 0, 1, -1, 0, 1], 9), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 2, -1, 0, 0], 9), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 0, -1, 1, 0], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 1, 0, 0, -1], 9), ([0, -1, 1, 2, -1, -1, 0], 9), ([0, -1, 1, 2, -1, 0, -1], -9), ([0, -1, 2, 1, -1, -1, 0], 9), ([0, -1, 2, 1, -1, 0, -1], 9), ([0, 0, 1, 1, -2, 0, 0], 18), ([1, -2, 1, 1, -1, 0, 1], 9), ([1, -2, 2, 1, -1, 0, 0], 9), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 0, 2, -1, 0, 0], 9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 1, 0, 0, 0, 0], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, -1, 1, 2, -1, -1, 0], 9), ([1, -1, 2, 0, -1, 0, 0], -9), ([1, -1, 2, 1, -1, -1, 0], 9), ([1, -1, 2, 1, -1, 0, -1], 9), ([1, 0, 1, 1, -2, 0, 0], 18)]

theorem source301_checked : normalize (row ![-1, 1, 1, -1, 0, 0] ![-1, 0, 0, 1, 0, 0] (3, 3)) = source301 := by
  decide +kernel

theorem source301_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source301 (momentValues f) = 0 := by
  rw [← source301_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source302 : Sparse := [([0, 0, -1, 0, 2, -1, 0], 18), ([0, 1, -2, 0, 1, -1, 1], 9), ([0, 1, -2, 0, 1, 0, 0], 9), ([0, 1, -2, 1, 1, -1, 0], -9), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, -1, 0, 0, 0, 0], 9), ([0, 1, -1, 0, 1, -2, 1], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 1, -1, 1, 1, -2, 0], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, -1, 1, -1, 0], 9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 2, -2, 0, 1, -1, 0], 9), ([0, 2, -1, 0, 1, -1, -1], 9), ([1, 0, -1, 0, 2, -1, 0], 18), ([1, 1, -2, 0, 1, -1, 1], 9), ([1, 1, -2, 0, 1, 0, 0], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 1, 0, 0], 9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, -1, 0, 1, -2, 1], 9), ([1, 1, -1, 1, 1, -2, 0], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 1, 0, 0, 0, -1, 0], 9), ([1, 1, 0, 0, 1, -2, 0], -9), ([1, 1, 0, 0, 1, -1, -1], 9), ([1, 2, -1, -1, 1, -1, 0], 9), ([1, 2, -1, 0, 1, -2, 0], 9)]

theorem source302_checked : normalize (row ![1, -1, 0, 1, -1, 0] ![1, 0, 0, -1, 0, 0] (3, 3)) = source302 := by
  decide +kernel

theorem source302_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source302 (momentValues f) = 0 := by
  rw [← source302_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source303 : Sparse := [([0, -2, 1, 0, -1, 1, 1], 9), ([0, -2, 1, 0, -1, 2, 0], -9), ([0, -2, 1, 1, -1, 1, 0], -9), ([0, -2, 2, 0, -1, 1, 0], 9), ([0, -1, 0, 0, -1, 2, 0], 9), ([0, -1, 0, 0, 0, 1, 0], -9), ([0, -1, 1, -1, 0, 1, 0], 9), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 1, 0, 0, 0, 0], 9), ([0, -1, 1, 0, 0, 1, -1], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 2, -1, -1, 1, 0], -9), ([1, -2, 1, 0, -1, 2, 0], -9), ([1, -2, 1, 1, -1, 1, 0], -9), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, -1, 0, 0, -1, 2, 0], 9), ([1, -1, 0, 0, 0, 1, 0], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, -1, 2, 0], -9), ([1, -1, 1, 0, -1, 2, -1], -9), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 2, 0, -1, 0, 0], -9), ([1, -1, 2, 0, -1, 1, -1], -9), ([1, 0, 1, 0, -2, 1, 0], -18)]

theorem source303_checked : normalize (row ![-1, 1, 0, -1, 1, 0] ![-1, 0, 0, 1, 0, 0] (0, -3)) = source303 := by
  decide +kernel

theorem source303_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source303 (momentValues f) = 0 := by
  rw [← source303_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
