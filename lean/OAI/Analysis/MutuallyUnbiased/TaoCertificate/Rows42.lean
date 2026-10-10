import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source336 : Sparse := [([0, -2, -1, 0, 1, 2, 0], 9), ([0, -2, -1, 1, 1, 1, 0], -9), ([0, -1, -2, 0, 1, 1, 1], -9), ([0, -1, -2, 0, 1, 2, 0], 9), ([0, -1, -1, -1, 1, 2, 0], -9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, -1, 0, 1, 2, -1], -9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 0, 0, 0, 1, 0], -9), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 0, 1, 1, -1], 9), ([1, -2, -1, 0, 1, 1, 1], -9), ([1, -2, 0, 0, 1, 1, 0], -9), ([1, -1, -2, 1, 1, 1, 0], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 1, 2, 0], -9), ([1, -1, -1, 0, 1, 2, -1], -9), ([1, -1, -1, 0, 2, 0, 0], -18), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, -1, 0, 0, 0, 1, 0], -9), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, 0, -2, 0, 1, 1, 0], -9), ([1, 0, -1, -1, 1, 1, 0], -9), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, -1, 0, 1, 1, -1], 9)]

theorem source336_checked : normalize (row ![-1, -1, 0, 1, 1, 0] ![0, 0, 0, -1, 1, 0] (0, -3)) = source336 := by
  decide +kernel

theorem source336_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source336 (momentValues f) = 0 := by
  rw [← source336_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source337 : Sparse := [([0, 0, 1, 1, -1, -1, 0], 9), ([0, 0, 2, 0, -1, -1, 0], 9), ([0, 1, 0, 0, -1, -1, 1], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, 0, -1, 0], 9), ([0, 1, 1, 0, -2, 0, 0], 18), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 2, -1, -1, -1, 0], 9), ([0, 1, 2, 0, -1, -2, 0], 9), ([0, 1, 2, 0, -1, -1, -1], -9), ([0, 2, 0, 0, -1, -1, 0], 9), ([0, 2, 1, -1, -1, -1, 0], -9), ([0, 2, 1, 0, -1, -2, 0], 9), ([0, 2, 1, 0, -1, -1, -1], 9), ([1, 0, 1, 0, -1, -1, 1], -9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 1, 1, -1, -1, 0], 9), ([1, 0, 2, 0, -1, -1, 0], 9), ([1, 1, 0, 0, -1, -1, 1], 9), ([1, 1, 0, 0, 0, -1, 0], 9), ([1, 1, 0, 1, -1, -1, 0], -9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, 0, -2, 0, 0], 18), ([1, 1, 1, 0, -1, -2, 1], 9), ([1, 1, 1, 1, -1, -2, 0], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 2, -1, -1, -1, 0], 9), ([1, 2, 0, 0, -1, -1, 0], 9), ([1, 2, 1, 0, -1, -1, -1], 9)]

theorem source337_checked : normalize (row ![1, 1, 0, -1, -1, 0] ![0, 0, 0, 1, -1, 0] (3, 3)) = source337 := by
  decide +kernel

theorem source337_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source337 (momentValues f) = 0 := by
  rw [← source337_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source338 : Sparse := [([0, -2, 0, -1, 1, 1, 1], 9), ([0, -2, 1, -1, 1, 1, 0], 9), ([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, 0, -2, 1, 1, 1], 9), ([0, -1, 0, -2, 1, 2, 0], 9), ([0, -1, 0, -1, 1, 2, -1], 9), ([0, -1, 0, -1, 2, 0, 0], 18), ([0, -1, 0, 0, 1, 1, -1], 9), ([0, -1, 1, -2, 1, 1, 0], -9), ([0, -1, 1, -1, 0, 1, 0], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, 0, -2, 1, 1, 0], 9), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 0, 0, -1, 1, 1, -1], -9), ([1, -2, 0, -1, 1, 1, 1], 9), ([1, -2, 0, -1, 1, 2, 0], 9), ([1, -2, 0, 0, 1, 1, 0], -9), ([1, -2, 1, -1, 1, 1, 0], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 1, 2, 0], 9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, 0, -2, 1, 1, 1], 9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 0, -1, 2, 0, 0], 18), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, 0, -1, -1, 1, 1, 0], 9), ([1, 0, 0, -2, 1, 1, 0], 9)]

theorem source338_checked : normalize (row ![-1, 0, -1, 1, 1, 0] ![0, 0, 0, -1, 1, 0] (3, 3)) = source338 := by
  decide +kernel

theorem source338_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source338 (momentValues f) = 0 := by
  rw [← source338_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source339 : Sparse := [([0, 0, 0, 1, -1, -1, 1], -9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 1, -1, 2, -1, -1, 0], -9), ([0, 1, 0, 0, 0, -1, 0], -9), ([0, 1, 0, 1, -1, -2, 1], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 1, 0, 2, -1, -2, 0], 9), ([0, 1, 1, 1, -1, -2, 0], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 2, 0, 0, -1, -1, 0], 9), ([0, 2, 0, 1, -1, -2, 0], -9), ([1, 0, 0, 2, -1, -1, 0], -9), ([1, 0, 1, 1, -1, -1, 0], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, 0, 0, -1, -1, 1], -9), ([1, 1, 0, 0, 0, -1, 0], -9), ([1, 1, 0, 1, -2, 0, 0], -18), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 1, 0, 2, -1, -1, -1], -9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 1, 1, 1, -1, -2, 0], -9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 2, -1, 1, -1, -1, 0], -9), ([1, 2, 0, 0, -1, -1, 0], 9), ([1, 2, 0, 1, -1, -2, 0], -9), ([1, 2, 0, 1, -1, -1, -1], -9)]

theorem source339_checked : normalize (row ![1, 0, 1, -1, -1, 0] ![0, 0, 0, 1, -1, 0] (0, -3)) = source339 := by
  decide +kernel

theorem source339_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source339 (momentValues f) = 0 := by
  rw [← source339_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source340 : Sparse := [([0, -2, 0, 0, 1, 2, -1], 9), ([0, -2, 0, 1, 1, 1, -1], -9), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, -1, 0, 1, 2, -1], 9), ([0, -1, 0, -1, 1, 2, -1], -9), ([0, -1, 0, 0, 0, 1, 0], 9), ([0, -1, 0, 0, 1, 2, -2], -9), ([0, -1, 0, 1, 0, 1, -1], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, 0, 1, -1], -9), ([0, 0, 0, 0, 0, 1, -1], -9), ([0, 0, 0, 0, 1, 1, -2], 9), ([1, -2, 0, 0, 1, 1, 0], -9), ([1, -2, 1, 0, 1, 1, -1], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, 0, -1, 1, 1, 0], -9), ([1, -1, 0, -1, 1, 2, -1], -9), ([1, -1, 0, 0, 1, 2, -2], -9), ([1, -1, 0, 0, 2, 0, -1], -18), ([1, -1, 0, 1, 1, 1, -2], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 1, 0, 1, 1, -2], -9), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 0, 0, 0, 0, 1, -1], -9), ([1, 0, 0, 0, 1, 1, -2], 9)]

theorem source340_checked : normalize (row ![-1, 0, 0, 1, 1, -1] ![0, 0, 0, -1, 1, 0] (0, -3)) = source340 := by
  decide +kernel

theorem source340_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source340 (momentValues f) = 0 := by
  rw [← source340_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source341 : Sparse := [([0, 0, 0, 1, -1, -1, 1], 9), ([0, 0, 1, 0, -1, -1, 1], 9), ([0, 1, -1, 0, -1, -1, 2], 9), ([0, 1, 0, -1, -1, -1, 2], 9), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 1, 0, 0, -2, 0, 1], 18), ([0, 1, 0, 0, 0, -1, 0], 9), ([0, 1, 0, 1, -1, -1, 0], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, 0, -1, -2, 1], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 2, -1, 0, -1, -1, 1], 9), ([0, 2, 0, -1, -1, -1, 1], -9), ([0, 2, 0, 0, -1, -2, 1], 9), ([0, 2, 0, 0, -1, -1, 0], 9), ([1, 0, 0, 0, -1, -1, 2], -9), ([1, 0, 0, 0, 0, -1, 1], 9), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 0, 1, 0, -1, -1, 1], 9), ([1, 1, -1, 0, -1, -1, 2], 9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, 0, -1, -1, -1, 2], 9), ([1, 1, 0, 0, -2, 0, 1], 18), ([1, 1, 0, 0, -1, -2, 2], 9), ([1, 1, 0, 1, -1, -2, 1], 9), ([1, 1, 0, 1, -1, -1, 0], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 2, -1, 0, -1, -1, 1], 9), ([1, 2, 0, 0, -1, -1, 0], 9)]

theorem source341_checked : normalize (row ![1, 0, 0, -1, -1, 1] ![0, 0, 0, 1, -1, 0] (3, 3)) = source341 := by
  decide +kernel

theorem source341_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source341 (momentValues f) = 0 := by
  rw [← source341_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source342 : Sparse := [([0, -1, -1, -1, 1, 2, 0], 9), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, 0, -2, -1, 1, 1, 1], -9), ([0, 0, -2, -1, 1, 2, 0], 9), ([0, 0, -1, -2, 1, 2, 0], -9), ([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, -1, -1, 1, 2, -1], -9), ([0, 0, -1, 0, 0, 1, 0], 9), ([0, 0, 0, -2, 1, 1, 0], 9), ([0, 0, 0, -1, 0, 1, 0], -9), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, -1, -1, 1, 1, -1], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, 0, -1, 1, 1, 0], -9), ([1, 0, -2, 0, 1, 1, 0], -9), ([1, 0, -1, -2, 1, 1, 1], -9), ([1, 0, -1, -2, 1, 2, 0], -9), ([1, 0, -1, -1, 1, 2, -1], -9), ([1, 0, -1, -1, 2, 0, 0], -18), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, 0, -2, 1, 1, 0], 9), ([1, 0, 0, -1, 0, 1, 0], -9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 1, -2, -1, 1, 1, 0], -9), ([1, 1, -1, -2, 1, 1, 0], -9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, -1, -1, 1, 1, -1], 9)]

theorem source342_checked : normalize (row ![0, -1, -1, 1, 1, 0] ![0, 0, 0, -1, 1, 0] (0, -3)) = source342 := by
  decide +kernel

theorem source342_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source342 (momentValues f) = 0 := by
  rw [← source342_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source343 : Sparse := [([0, -1, 1, 2, -1, -1, 0], 9), ([0, -1, 2, 1, -1, -1, 0], 9), ([0, 0, 0, 1, -1, -1, 1], 9), ([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 1, 0, 0, -1, 0], 9), ([0, 0, 1, 1, -2, 0, 0], 18), ([0, 0, 1, 1, 0, -1, -1], 9), ([0, 0, 1, 2, -1, -1, -1], 9), ([0, 0, 2, 0, -1, -1, 0], 9), ([0, 0, 2, 1, -1, -2, 0], 9), ([0, 0, 2, 1, -1, -1, -1], -9), ([0, 1, 0, 1, -1, -1, 0], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 1, 1, 1, -1, -2, 0], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, -1, 1, 2, -1, -1, 0], 9), ([1, -1, 2, 1, -1, -1, 0], 9), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 0, 0, 1, 0, -1, 0], 9), ([1, 0, 0, 2, -1, -1, 0], -9), ([1, 0, 1, 0, -1, -1, 1], 9), ([1, 0, 1, 1, -2, 0, 0], 18), ([1, 0, 1, 1, -1, -2, 1], 9), ([1, 0, 1, 2, -1, -2, 0], 9), ([1, 0, 1, 2, -1, -1, -1], 9), ([1, 0, 2, 0, -1, -1, 0], 9), ([1, 1, 0, 1, -1, -1, 0], 9), ([1, 1, 1, 1, -1, -1, -1], 9)]

theorem source343_checked : normalize (row ![0, 1, 1, -1, -1, 0] ![0, 0, 0, 1, -1, 0] (3, 3)) = source343 := by
  decide +kernel

theorem source343_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source343 (momentValues f) = 0 := by
  rw [← source343_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
