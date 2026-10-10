import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source144 : Sparse := [([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 1, -2, -1, 1, 0, 1], 9), ([0, 1, -2, -1, 1, 1, 0], -9), ([0, 1, -2, -1, 2, 0, 0], 9), ([0, 1, -2, 0, 1, 0, 0], 9), ([0, 1, -1, -2, 1, 0, 1], 9), ([0, 1, -1, -2, 1, 1, 0], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, -1, 2, 0, -1], 9), ([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 1, 0, -1, 1, -1, 0], 9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 2, -1, -1, 0, 0, 0], 18), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, 0, -1, 1, 0, 0], 9), ([1, 1, -2, -1, 1, 0, 1], 9), ([1, 1, -2, 0, 1, 0, 0], 9), ([1, 1, -1, -2, 1, 0, 1], 9), ([1, 1, -1, -2, 1, 1, 0], 9), ([1, 1, -1, -2, 2, 0, 0], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, -1, 2, -1, 0], 9), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, 0, -2, 1, 0, 0], -9), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 1, 0, -1, 1, 0, -1], 9), ([1, 2, -1, -1, 0, 0, 0], 18)]

theorem source144_checked : normalize (row ![1, -1, -1, 1, 0, 0] ![-1, 0, 0, 1, 0, 0] (3, 3)) = source144 := by
  decide +kernel

theorem source144_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source144 (momentValues f) = 0 := by
  rw [← source144_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source145 : Sparse := [([0, -1, 0, 2, -1, 0, 0], 9), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 1, 1, -2, 0, 1], 9), ([0, -1, 1, 1, -2, 1, 0], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 2, -2, 0, 0], -9), ([0, -1, 2, 1, -2, 0, 0], 9), ([0, -1, 2, 1, -1, -1, 0], -9), ([0, 0, 0, 1, -1, 0, 0], -9), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 0, 1, 1, -1, 0, -1], -9), ([1, -2, 1, 1, 0, 0, 0], -18), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 0, 2, -1, 0, 0], 9), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 1, 1, -2, 1, 0], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 2, -2, 0, 0], -9), ([1, -1, 1, 2, -1, -1, 0], -9), ([1, -1, 1, 2, -1, 0, -1], -9), ([1, -1, 2, 0, -1, 0, 0], -9), ([1, -1, 2, 1, -1, 0, -1], -9), ([1, 0, 0, 1, -1, 0, 0], -9), ([1, 0, 1, 1, -1, 0, -1], -9)]

theorem source145_checked : normalize (row ![-1, 1, 1, -1, 0, 0] ![1, 0, 0, -1, 0, 0] (0, -3)) = source145 := by
  decide +kernel

theorem source145_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source145 (momentValues f) = 0 := by
  rw [← source145_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source146 : Sparse := [([0, 0, -1, 0, 1, -1, 1], 9), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 1, -2, 0, 1, 0, 0], 9), ([0, 1, -2, 0, 2, -1, 0], -9), ([0, 1, -1, -1, 2, -1, 0], 9), ([0, 1, -1, 0, 1, -2, 1], -9), ([0, 1, -1, 0, 2, -2, 0], 9), ([0, 1, -1, 0, 2, -1, -1], -9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, -1, 1, -1, 0], -9), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 1, -2, 0, 1, -1, 1], -9), ([1, 1, -2, 0, 1, 0, 0], 9), ([1, 1, -2, 0, 2, -1, 0], -9), ([1, 1, -2, 1, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 1, 0, 0], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, -1, 0, 2, -1, -1], -9), ([1, 1, -1, 1, 1, -2, 0], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, 0, 1, -2, 0], -9), ([1, 1, 0, 0, 1, -1, -1], -9), ([1, 2, -1, 0, 0, -1, 0], -18)]

theorem source146_checked : normalize (row ![1, -1, 0, 1, -1, 0] ![-1, 0, 0, 1, 0, 0] (0, -3)) = source146 := by
  decide +kernel

theorem source146_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source146 (momentValues f) = 0 := by
  rw [← source146_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source147 : Sparse := [([0, -2, 1, 0, 0, 1, 0], 18), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, -1, 0, 0, -1, 2, 0], 9), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 1, -1, -1, 2, 0], 9), ([0, -1, 1, 0, -2, 2, 0], 9), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 0, -1, 2, -1], -9), ([0, -1, 1, 1, -2, 1, 0], 9), ([0, -1, 1, 1, -1, 0, 0], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 2, -1, -1, 1, 0], 9), ([0, -1, 2, 0, -1, 1, -1], 9), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 0, 1, 0, -1, 1, -1], 9), ([1, -2, 1, 0, 0, 1, 0], 18), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, -1, 0, 0, -1, 2, 0], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, -1, 2, 0], 9), ([1, -1, 1, 0, -2, 1, 1], 9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 2, -1, -1, 1, 0], 9), ([1, -1, 2, 0, -2, 1, 0], 9), ([1, -1, 2, 0, -1, 0, 0], -9), ([1, -1, 2, 0, -1, 1, -1], 9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 0, 1, 0, -1, 0, 0], 9)]

theorem source147_checked : normalize (row ![-1, 1, 0, -1, 1, 0] ![1, 0, 0, -1, 0, 0] (3, 3)) = source147 := by
  decide +kernel

theorem source147_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source147 (momentValues f) = 0 := by
  rw [← source147_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source148 : Sparse := [([0, 0, -1, 0, 1, 1, -1], 9), ([0, 0, -1, 1, 1, 0, -1], 9), ([0, 1, -2, 0, 1, 0, 0], 9), ([0, 1, -2, 0, 1, 1, -1], -9), ([0, 1, -2, 0, 2, 0, -1], 9), ([0, 1, -2, 1, 1, 0, -1], 9), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, 1, 1, -2], 9), ([0, 1, -1, 0, 2, 0, -2], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, -1, 1, 1, 0, -2], -9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 1, 0, 0, 1, 0, -2], 9), ([0, 2, -1, 0, 0, 0, -1], 18), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, 0, 0, 1, 0, -1], 9), ([1, 1, -2, 0, 1, 0, 0], 9), ([1, 1, -2, 1, 1, 0, -1], 9), ([1, 1, -1, -1, 1, 0, 0], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, -1, 2, 0, -1], 9), ([1, 1, -1, 0, 1, -1, 0], -9), ([1, 1, -1, 0, 1, 1, -2], 9), ([1, 1, -1, 0, 2, -1, -1], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, -1, 1, 0, -1], -9), ([1, 1, 0, 0, 1, -1, -1], 9), ([1, 1, 0, 0, 1, 0, -2], 9), ([1, 2, -1, 0, 0, 0, -1], 18)]

theorem source148_checked : normalize (row ![1, -1, 0, 1, 0, -1] ![-1, 0, 0, 1, 0, 0] (3, 3)) = source148 := by
  decide +kernel

theorem source148_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source148 (momentValues f) = 0 := by
  rw [← source148_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source149 : Sparse := [([0, -1, 0, 1, -1, 0, 1], 9), ([0, -1, 1, -1, -1, 0, 2], -9), ([0, -1, 1, 0, -2, 0, 2], 9), ([0, -1, 1, 0, -2, 1, 1], -9), ([0, -1, 1, 0, -1, 1, 0], 9), ([0, -1, 1, 1, -2, 0, 1], -9), ([0, -1, 2, 0, -2, 0, 1], 9), ([0, -1, 2, 0, -1, -1, 1], -9), ([0, 0, 0, 0, -1, 0, 1], -9), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 1, 0, -1, 0, 0], -9), ([1, -2, 1, 0, 0, 0, 1], -18), ([1, -1, 0, 0, -1, 0, 2], -9), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, 0, -2, 1, 1], -9), ([1, -1, 1, 0, -1, -1, 2], -9), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 1, 1, -2, 0, 1], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 2, -1, -1, 0, 1], -9), ([1, -1, 2, 0, -1, 0, 0], -9), ([1, 0, 0, 0, -1, 0, 1], -9), ([1, 0, 1, 0, -1, 0, 0], -9)]

theorem source149_checked : normalize (row ![-1, 1, 0, -1, 0, 1] ![1, 0, 0, -1, 0, 0] (0, -3)) = source149 := by
  decide +kernel

theorem source149_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source149 (momentValues f) = 0 := by
  rw [← source149_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source150 : Sparse := [([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, -1, -1, 2, -1, 0], -9), ([0, 1, 0, -2, 2, -1, 0], 9), ([0, 1, 0, -1, 1, -2, 1], -9), ([0, 1, 0, -1, 2, -2, 0], 9), ([0, 1, 0, -1, 2, -1, -1], -9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 1, 1, -2, 1, -1, 0], -9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 1, 0, 0], 9), ([1, 1, -1, -1, 2, -1, 0], -9), ([1, 1, -1, 0, 1, -1, 0], -9), ([1, 1, 0, -2, 1, -1, 1], -9), ([1, 1, 0, -2, 1, 0, 0], -9), ([1, 1, 0, -1, 1, 0, -1], -9), ([1, 1, 0, -1, 2, -1, -1], -9), ([1, 1, 0, 0, 1, -2, 0], -9), ([1, 1, 0, 0, 1, -1, -1], 9), ([1, 1, 1, -1, 1, -2, 0], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 2, 0, -1, 0, -1, 0], -18)]

theorem source150_checked : normalize (row ![1, 0, -1, 1, -1, 0] ![-1, 0, 0, 1, 0, 0] (0, -3)) = source150 := by
  decide +kernel

theorem source150_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source150 (momentValues f) = 0 := by
  rw [← source150_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source151 : Sparse := [([0, -2, 0, 1, 0, 1, 0], 18), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, -1, 2, 0], 9), ([0, -1, -1, 2, -1, 1, 0], -9), ([0, -1, 0, 0, -1, 2, 0], 9), ([0, -1, 0, 1, -2, 2, 0], 9), ([0, -1, 0, 1, -1, 0, 1], 9), ([0, -1, 0, 1, -1, 2, -1], -9), ([0, -1, 0, 2, -2, 1, 0], 9), ([0, -1, 0, 2, -1, 0, 0], 9), ([0, -1, 0, 2, -1, 1, -1], 9), ([0, -1, 1, 0, -1, 1, 0], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, 0, 1, -1, 1, -1], 9), ([1, -2, 0, 1, 0, 1, 0], 18), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, -1, 2, 0], 9), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, -1, 0, 0, -1, 2, 0], 9), ([1, -1, 0, 1, -2, 1, 1], 9), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 0, 2, -1, 0, 0], 9), ([1, -1, 0, 2, -1, 1, -1], 9), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 1, 1, -2, 1, 0], 9), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 0, 0, 1, -1, 0, 0], 9)]

theorem source151_checked : normalize (row ![-1, 0, 1, -1, 1, 0] ![1, 0, 0, -1, 0, 0] (3, 3)) = source151 := by
  decide +kernel

theorem source151_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source151 (momentValues f) = 0 := by
  rw [← source151_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
