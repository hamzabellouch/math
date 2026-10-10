import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source160 : Sparse := [([0, 0, -1, 0, 0, 1, 0], 9), ([0, 0, -1, 0, 1, 1, -1], 9), ([0, 1, -2, 0, 0, 1, 0], 9), ([0, 1, -2, 0, 0, 2, -1], 9), ([0, 1, -2, 0, 1, 1, -1], -9), ([0, 1, -2, 1, 0, 1, -1], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, -1, -1, 0, 2, -1], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, -1, 1, 0], 9), ([0, 1, -1, 0, 1, 1, -2], 9), ([0, 1, -1, 1, 0, 1, -2], 9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 1, 0, 0, -1, 1, -1], 9), ([0, 2, -1, 0, 0, 0, -1], 18), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 0, 0, 0, 0, 1, -1], 9), ([1, 1, -2, 0, 0, 1, 0], 9), ([1, 1, -2, 1, 0, 1, -1], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, -1, 1, 0], 9), ([1, 1, -1, 0, -1, 2, -1], 9), ([1, 1, -1, 0, 0, 2, -2], 9), ([1, 1, -1, 0, 1, 1, -2], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, 1, -2], 9), ([1, 1, 0, -1, 0, 1, -1], 9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 1, 0, 0, 0, 1, -2], -9), ([1, 2, -1, 0, 0, 0, -1], 18)]

theorem source160_checked : normalize (row ![1, -1, 0, 0, 1, -1] ![-1, 0, 0, 0, 1, 0] (3, 3)) = source160 := by
  decide +kernel

theorem source160_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source160 (momentValues f) = 0 := by
  rw [← source160_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source161 : Sparse := [([0, -1, 0, 0, 0, -1, 2], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, 0, 0, -2, 2], -9), ([0, -1, 1, 0, 1, -2, 1], -9), ([0, -1, 1, 1, 0, -2, 1], 9), ([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 2, 0, -1, -1, 1], -9), ([0, -1, 2, 0, 0, -2, 1], 9), ([0, 0, 0, 0, 0, -1, 1], -9), ([0, 0, 1, -1, 0, -1, 1], -9), ([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 1, 0, 0, -1, 0], 9), ([1, -2, 1, 0, 0, 0, 1], -18), ([1, -1, 0, 0, 0, -1, 2], 9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 1, -1, 0, -1, 2], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, -1, -1, 2], -9), ([1, -1, 1, 0, 0, -2, 2], -9), ([1, -1, 1, 0, 1, -2, 1], -9), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 2, -1, 0, -1, 1], -9), ([1, -1, 2, 0, 0, -1, 0], -9), ([1, 0, 0, 0, 0, -1, 1], -9), ([1, 0, 1, -1, 0, -1, 1], -9)]

theorem source161_checked : normalize (row ![-1, 1, 0, 0, -1, 1] ![1, 0, 0, 0, -1, 0] (0, -3)) = source161 := by
  decide +kernel

theorem source161_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source161 (momentValues f) = 0 := by
  rw [← source161_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source162 : Sparse := [([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, -1, 2, 0], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, -1, 0, -1, 1, 0], 9), ([0, 1, 0, -2, -1, 1, 1], -9), ([0, 1, 0, -2, -1, 2, 0], 9), ([0, 1, 0, -2, 0, 1, 0], 9), ([0, 1, 0, -1, -2, 1, 1], 9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 1, 0, 0, -1, 1, -1], 9), ([0, 1, 1, -2, -1, 1, 0], 9), ([0, 1, 1, -1, -2, 1, 0], 9), ([0, 2, 0, -1, -1, 0, 0], 18), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, 0, -1, 1, 0], 9), ([1, 1, 0, -2, 0, 1, 0], 9), ([1, 1, 0, -1, -2, 1, 1], 9), ([1, 1, 0, -1, -2, 2, 0], 9), ([1, 1, 0, -1, -1, 2, -1], 9), ([1, 1, 0, -1, 0, 1, -1], 9), ([1, 1, 0, 0, -2, 1, 0], -9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 1, 1, -2, -1, 1, 0], 9), ([1, 1, 1, -1, -2, 1, 0], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 2, 0, -1, -1, 0, 0], 18)]

theorem source162_checked : normalize (row ![1, 0, -1, -1, 1, 0] ![-1, 0, 0, 0, 1, 0] (3, 3)) = source162 := by
  decide +kernel

theorem source162_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source162 (momentValues f) = 0 := by
  rw [← source162_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source163 : Sparse := [([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, 0, 0, 2, -1, 0], 9), ([0, -1, 0, 1, 1, -2, 1], -9), ([0, -1, 0, 1, 2, -2, 0], -9), ([0, -1, 0, 2, 1, -2, 0], 9), ([0, -1, 0, 2, 1, -1, -1], -9), ([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 1, 1, 1, -2, 0], 9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 0, 1, 1, -1, -1], 9), ([1, -2, 0, 1, 1, 0, 0], -18), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 2, -1, 0], -9), ([1, -1, -1, 2, 1, -1, 0], -9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, -1, 0, 0, 2, -1, 0], 9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 0, 1, 1, -2, 1], -9), ([1, -1, 0, 1, 2, -2, 0], -9), ([1, -1, 0, 1, 2, -1, -1], -9), ([1, -1, 0, 2, 0, -1, 0], -9), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 0, 0, 0, 1, -1, 0], -9)]

theorem source163_checked : normalize (row ![-1, 0, 1, 1, -1, 0] ![1, 0, 0, 0, -1, 0] (0, -3)) = source163 := by
  decide +kernel

theorem source163_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source163 (momentValues f) = 0 := by
  rw [← source163_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source164 : Sparse := [([0, 0, 0, -1, 0, 1, 0], -9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 0, 0, 0, 0, 1, -1], 9), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 1, -1, -1, 0, 2, -1], -9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, 0, -2, 0, 1, 0], 9), ([0, 1, 0, -2, 0, 2, -1], -9), ([0, 1, 0, -1, -1, 2, -1], 9), ([0, 1, 0, -1, 0, 2, -2], 9), ([0, 1, 0, 0, -1, 1, -1], -9), ([0, 1, 1, -1, 0, 1, -2], -9), ([1, 0, 0, -1, 0, 1, 0], -9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, -1, -1, 0, 2, -1], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, 0, -2, 0, 1, 0], 9), ([1, 1, 0, -2, 0, 2, -1], -9), ([1, 1, 0, -2, 1, 1, -1], -9), ([1, 1, 0, -1, -1, 1, 0], -9), ([1, 1, 0, -1, 1, 1, -2], -9), ([1, 1, 0, 0, 0, 1, -2], -9), ([1, 1, 1, -2, 0, 1, -1], -9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 2, 0, -1, 0, 0, -1], -18)]

theorem source164_checked : normalize (row ![1, 0, -1, 0, 1, -1] ![-1, 0, 0, 0, 1, 0] (0, -3)) = source164 := by
  decide +kernel

theorem source164_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source164 (momentValues f) = 0 := by
  rw [← source164_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source165 : Sparse := [([0, -2, 0, 1, 0, 0, 1], 18), ([0, -1, -1, 1, 0, -1, 2], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 2, 0, -1, 1], 9), ([0, -1, 0, 0, 0, -1, 2], 9), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 0, 1, -1, -1, 2], 9), ([0, -1, 0, 1, 0, -2, 2], 9), ([0, -1, 0, 1, 1, -2, 1], 9), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, -1, 0, 2, -1, -1, 1], 9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, 0, 0, 0, -1, 1], 9), ([1, -2, 0, 1, 0, 0, 1], 18), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 2, 0, -1, 1], 9), ([1, -1, 0, 0, 0, -1, 2], 9), ([1, -1, 0, 1, -1, -1, 2], 9), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 0, 2, -1, -1, 1], 9), ([1, -1, 0, 2, 0, -2, 1], 9), ([1, -1, 0, 2, 0, -1, 0], -9), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, 0, -2, 1], 9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 0, 0, 1, 0, -1, 0], 9)]

theorem source165_checked : normalize (row ![-1, 0, 1, 0, -1, 1] ![1, 0, 0, 0, -1, 0] (3, 3)) = source165 := by
  decide +kernel

theorem source165_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source165 (momentValues f) = 0 := by
  rw [← source165_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source166 : Sparse := [([0, 0, 0, 0, -1, 1, 0], -9), ([0, 0, 0, 0, 0, 1, -1], -9), ([0, 0, 0, 1, -1, 1, -1], 9), ([0, 0, 1, 0, -1, 1, -1], 9), ([0, 1, -1, 0, -1, 2, -1], -9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 1, 0, -1, -1, 2, -1], -9), ([0, 1, 0, 0, -2, 2, -1], 9), ([0, 1, 0, 0, -1, 2, -2], 9), ([0, 1, 0, 1, -2, 1, -1], -9), ([0, 1, 1, 0, -1, 1, -2], -9), ([1, 0, 0, 0, -1, 1, 0], -9), ([1, 0, 0, 0, 0, 1, -1], -9), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 0, -1, 2, -1], -9), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, 0, -1, -1, 1, 0], 9), ([1, 1, 0, -1, -1, 2, -1], -9), ([1, 1, 0, -1, 0, 1, -1], -9), ([1, 1, 0, 0, -2, 1, 0], -9), ([1, 1, 0, 0, 0, 1, -2], -9), ([1, 1, 0, 1, -1, 1, -2], -9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, 0, -2, 1, -1], -9), ([1, 2, 0, 0, -1, 0, -1], -18)]

theorem source166_checked : normalize (row ![1, 0, 0, -1, 1, -1] ![-1, 0, 0, 0, 1, 0] (0, -3)) = source166 := by
  decide +kernel

theorem source166_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source166 (momentValues f) = 0 := by
  rw [← source166_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source167 : Sparse := [([0, -2, 0, 0, 1, 0, 1], 18), ([0, -1, -1, 0, 1, -1, 2], -9), ([0, -1, -1, 0, 2, -1, 1], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, 0, -1, 1, -1, 2], 9), ([0, -1, 0, -1, 2, -1, 1], -9), ([0, -1, 0, 0, 0, -1, 2], 9), ([0, -1, 0, 0, 1, -2, 2], 9), ([0, -1, 0, 0, 2, -2, 1], 9), ([0, -1, 0, 0, 2, -1, 0], 9), ([0, -1, 0, 1, 0, -1, 1], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, 0, -1, 0, 1, -1, 1], 9), ([0, 0, 0, -1, 1, -1, 1], 9), ([1, -2, 0, 0, 1, 0, 1], 18), ([1, -1, -1, 0, 2, -1, 1], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, 0, -1, 1, -1, 2], 9), ([1, -1, 0, 0, 0, -1, 2], 9), ([1, -1, 0, 0, 2, -1, 0], 9), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, -1, 0, 1, 1, -2, 1], 9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 0, 1, -2, 1], 9), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, 0, 0, 0, 0, -1, 1], 9), ([1, 0, 0, 0, 1, -1, 0], 9)]

theorem source167_checked : normalize (row ![-1, 0, 0, 1, -1, 1] ![1, 0, 0, 0, -1, 0] (3, 3)) = source167 := by
  decide +kernel

theorem source167_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source167 (momentValues f) = 0 := by
  rw [← source167_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
