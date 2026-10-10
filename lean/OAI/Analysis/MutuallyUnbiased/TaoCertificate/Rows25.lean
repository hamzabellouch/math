import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source200 : Sparse := [([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 1, 0, 0, -1], 9), ([0, 0, 0, 1, -1, 1, -1], 9), ([0, 0, 1, 1, -2, 0, 0], 9), ([0, 0, 1, 1, -2, 1, -1], 9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 0, 1, 1, -1, 1, -2], -9), ([0, 0, 1, 1, 0, 0, -2], 9), ([0, 0, 1, 2, -2, 0, -1], 9), ([0, 0, 1, 2, -1, 0, -2], 9), ([0, 0, 2, 0, -1, 0, -1], 18), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 1, 1, 1, -2, 0, -1], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, -1, 0, -2], 9), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 2, -1, 0, -1], 9), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 0, 1, 1, -2, 0, 0], 9), ([1, 0, 1, 1, -2, 1, -1], 9), ([1, 0, 1, 1, -1, -1, 0], 9), ([1, 0, 1, 1, 0, -1, -1], -9), ([1, 0, 1, 1, 0, 0, -2], 9), ([1, 0, 1, 2, -1, -1, -1], 9), ([1, 0, 2, 0, -1, 0, -1], 18), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, -1, 0, -2], 9)]

theorem source200_checked : normalize (row ![0, 1, 1, -1, 0, -1] ![0, -1, 1, 0, 0, 0] (3, 3)) = source200 := by
  decide +kernel

theorem source200_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source200 (momentValues f) = 0 := by
  rw [← source200_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source201 : Sparse := [([0, -1, -1, -1, 2, 0, 1], -9), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, 0, -1, -2, 1, 0, 2], 9), ([0, 0, -1, -2, 1, 1, 1], -9), ([0, 0, -1, -2, 2, 0, 1], 9), ([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, -1, -1, 1, -1, 2], -9), ([0, 0, 0, -1, 0, 0, 1], -9), ([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 1, -1, -2, 1, 0, 1], -9), ([0, 1, -1, -1, 1, 0, 0], 9), ([1, -1, -1, -1, 1, 0, 2], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, 0, -2, 0, 1, 0, 1], -18), ([1, 0, -1, -2, 1, 1, 1], -9), ([1, 0, -1, -1, 0, 0, 2], -9), ([1, 0, -1, -1, 0, 1, 1], 9), ([1, 0, -1, -1, 1, 1, 0], -9), ([1, 0, -1, -1, 2, -1, 1], -9), ([1, 0, -1, -1, 2, 0, 0], -9), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 1, -1, -2, 1, 0, 1], -9), ([1, 1, -1, -1, 0, 0, 1], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 1, 0, 0], 9)]

theorem source201_checked : normalize (row ![0, -1, -1, 1, 0, 1] ![0, 1, -1, 0, 0, 0] (0, -3)) = source201 := by
  decide +kernel

theorem source201_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source201 (momentValues f) = 0 := by
  rw [← source201_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source202 : Sparse := [([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 1, 2, 0, -1, -1], 9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 0, 0, 1, 1, -1, -1], 9), ([0, 0, 1, 1, 0, 0, -2], 9), ([0, 0, 1, 1, 1, -2, -1], -9), ([0, 0, 1, 2, -1, -1, -1], -9), ([0, 0, 1, 2, 0, -2, -1], 9), ([0, 0, 1, 2, 0, -1, -2], -9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 1, 1, -1, -1, 0], -9), ([1, 0, 1, 1, -1, 0, -1], -9), ([1, 0, 1, 1, 0, -2, 0], -9), ([1, 0, 1, 1, 0, 0, -2], 9), ([1, 0, 1, 1, 1, -1, -2], -9), ([1, 0, 1, 2, -1, -1, -1], -9), ([1, 0, 1, 2, 0, -1, -2], -9), ([1, 0, 2, 0, 0, -1, -1], -18), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, 0, -2, -1], -9), ([1, 1, 1, 1, 0, -1, -2], -9)]

theorem source202_checked : normalize (row ![0, 1, 1, 0, -1, -1] ![0, -1, 1, 0, 0, 0] (0, -3)) = source202 := by
  decide +kernel

theorem source202_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source202 (momentValues f) = 0 := by
  rw [← source202_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source203 : Sparse := [([0, -1, -1, -1, 0, 1, 2], 9), ([0, -1, -1, -1, 0, 2, 1], 9), ([0, 0, -2, 0, 0, 1, 1], 18), ([0, 0, -1, -2, 0, 2, 1], 9), ([0, 0, -1, -1, -1, 1, 2], 9), ([0, 0, -1, -1, -1, 2, 1], -9), ([0, 0, -1, -1, 0, 2, 0], 9), ([0, 0, -1, -1, 1, 0, 1], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 1, -1, -2, 0, 1, 1], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 0, 0, 1], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([1, -1, -1, -1, 0, 1, 2], 9), ([1, -1, -1, -1, 0, 2, 1], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, 0, -2, 0, 0, 1, 1], 18), ([1, 0, -1, -2, 0, 1, 2], 9), ([1, 0, -1, -2, 1, 1, 1], 9), ([1, 0, -1, -1, -1, 1, 2], 9), ([1, 0, -1, -1, 0, 0, 2], -9), ([1, 0, -1, -1, 0, 2, 0], 9), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, -1, -1, 1, 1, 0], 9), ([1, 0, 0, -1, 0, 0, 1], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, 0, 0, 1], 9)]

theorem source203_checked : normalize (row ![0, -1, -1, 0, 1, 1] ![0, 1, -1, 0, 0, 0] (3, 3)) = source203 := by
  decide +kernel

theorem source203_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source203 (momentValues f) = 0 := by
  rw [← source203_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source204 : Sparse := [([0, -2, 1, -1, 1, 0, 1], 9), ([0, -2, 1, -1, 1, 1, 0], -9), ([0, -2, 1, -1, 2, 0, 0], 9), ([0, -2, 1, 0, 1, 0, 0], 9), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 1, -2, 1, 0, 1], -9), ([0, -1, 1, -2, 1, 1, 0], 9), ([0, -1, 1, -2, 2, 0, 0], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, 1, 0, -1], 9), ([0, -1, 2, -1, 0, 0, 0], 18), ([0, 0, 1, -2, 1, 0, 0], 9), ([0, 0, 1, -1, 1, -1, 0], 9), ([1, -2, 1, -1, 1, 0, 1], 9), ([1, -2, 1, 0, 1, 0, 0], 9), ([1, -1, 0, 0, 1, 0, 0], 9), ([1, -1, 1, -2, 1, 1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, -1, 2, -1, 0], 9), ([1, -1, 1, -1, 2, 0, -1], 9), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, -1, 2, -1, 0, 0, 0], 18), ([1, 0, 0, -1, 1, 0, 0], 9), ([1, 0, 1, -2, 1, 0, 0], 9), ([1, 0, 1, -1, 1, -1, 0], 9), ([1, 0, 1, -1, 1, 0, -1], -9)]

theorem source204_checked : normalize (row ![-1, 1, -1, 1, 0, 0] ![0, -1, 0, 1, 0, 0] (3, 3)) = source204 := by
  decide +kernel

theorem source204_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source204 (momentValues f) = 0 := by
  rw [← source204_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source205 : Sparse := [([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, 0, 1, -1, 0, 0], -9), ([0, 1, -1, 0, -1, 1, 0], 9), ([0, 1, -1, 1, -2, 0, 1], -9), ([0, 1, -1, 1, -2, 1, 0], -9), ([0, 1, -1, 2, -2, 0, 0], 9), ([0, 1, -1, 2, -1, 0, -1], -9), ([0, 1, 0, 0, -1, 0, 0], -9), ([0, 1, 0, 1, -1, -1, 0], 9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 2, -1, 1, -2, 0, 0], 9), ([0, 2, -1, 1, -1, -1, 0], -9), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 0, -1, 2, -1, 0, 0], -9), ([1, 0, 0, 1, -1, 0, 0], -9), ([1, 1, -2, 1, 0, 0, 0], -18), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, -1, 0, -1, 1, 0], 9), ([1, 1, -1, 1, -2, 0, 1], -9), ([1, 1, -1, 1, -2, 1, 0], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 2, -1, -1, 0], -9), ([1, 1, 0, 0, -1, 0, 0], -9), ([1, 2, -1, 0, -1, 0, 0], -9), ([1, 2, -1, 1, -1, 0, -1], -9)]

theorem source205_checked : normalize (row ![1, -1, 1, -1, 0, 0] ![0, 1, 0, -1, 0, 0] (0, -3)) = source205 := by
  decide +kernel

theorem source205_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source205 (momentValues f) = 0 := by
  rw [← source205_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source206 : Sparse := [([0, -2, 1, 0, 1, 0, 0], 9), ([0, -2, 1, 0, 2, -1, 0], -9), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 2, -1, 0], -9), ([0, -1, 1, 0, 2, -2, 0], 9), ([0, -1, 1, 0, 2, -1, -1], 9), ([0, -1, 1, 1, 1, -2, 0], -9), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 0, 1, 0, 1, -1, -1], -9), ([1, -2, 1, 0, 1, -1, 1], -9), ([1, -2, 1, 0, 1, 0, 0], 9), ([1, -2, 1, 0, 2, -1, 0], -9), ([1, -2, 1, 1, 1, -1, 0], -9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 1, -1, 2, -1, 0], -9), ([1, -1, 1, 0, 1, -2, 1], -9), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 2, 0, 0, -1, 0], -18), ([1, 0, 1, -1, 1, -1, 0], -9), ([1, 0, 1, 0, 1, -2, 0], -9)]

theorem source206_checked : normalize (row ![-1, 1, 0, 1, -1, 0] ![0, -1, 0, 1, 0, 0] (0, -3)) = source206 := by
  decide +kernel

theorem source206_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source206 (momentValues f) = 0 := by
  rw [← source206_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source207 : Sparse := [([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, -1, 0, -1, 2, 0], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 1, -2, 0, 0, 1, 0], 18), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, -1, 2, 0], -9), ([0, 1, -1, 0, -2, 1, 1], 9), ([0, 1, -1, 0, -2, 2, 0], 9), ([0, 1, -1, 0, -1, 0, 1], 9), ([0, 1, -1, 0, -1, 2, -1], 9), ([0, 1, -1, 1, -1, 0, 0], 9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 2, -1, -1, -1, 1, 0], 9), ([0, 2, -1, 0, -1, 1, -1], 9), ([1, 0, -1, 0, -1, 2, 0], 9), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 1, -2, 0, 0, 1, 0], 18), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 0, -1, 2, -1], 9), ([1, 1, -1, 1, -2, 1, 0], 9), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, 0, 0, -1, 0, 0], 9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 2, -1, -1, -1, 1, 0], 9), ([1, 2, -1, 0, -2, 1, 0], 9), ([1, 2, -1, 0, -1, 0, 0], -9), ([1, 2, -1, 0, -1, 1, -1], 9)]

theorem source207_checked : normalize (row ![1, -1, 0, -1, 1, 0] ![0, 1, 0, -1, 0, 0] (3, 3)) = source207 := by
  decide +kernel

theorem source207_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source207 (momentValues f) = 0 := by
  rw [← source207_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
