import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source96 : Sparse := [([0, 0, -1, 0, 1, 1, -1], -36), ([0, 1, -2, 0, 0, 1, 0], -36), ([0, 1, -2, 0, 0, 2, -1], -36), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, -1, 1, 1, -1], -36), ([0, 1, -1, 0, -1, 1, 0], -36), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, 0, -1, 0, 1, -1], -36), ([0, 2, -2, 0, 0, 1, -1], 36), ([0, 2, -1, 0, 0, 0, -1], -36), ([0, 2, -1, 0, 0, 1, -2], -36), ([1, 0, -1, 0, 0, 2, -1], 36), ([1, 0, -1, 1, 0, 1, -1], -36), ([1, 1, -2, 0, 0, 1, 0], -36), ([1, 1, -1, -1, 0, 1, 0], 36), ([1, 1, -1, -1, 1, 1, -1], -36), ([1, 1, -1, 0, 0, 2, -2], -36), ([1, 1, -1, 0, 1, 0, -1], 36), ([1, 1, -1, 1, -1, 1, -1], 36), ([1, 1, 0, 0, -1, 1, -1], -36), ([1, 1, 0, 0, 0, 1, -2], 36), ([1, 2, -2, 0, 0, 1, -1], 36), ([1, 2, -1, 0, 0, 0, -1], -36)]

theorem source96_checked : normalize (row ![1, -1, 0, 0, 1, -1] ![1, -1, 0, 0, 1, -1] (-12, 0)) = source96 := by
  decide +kernel

theorem source96_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source96 (momentValues f) = 0 := by
  rw [← source96_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source97 : Sparse := [([0, 0, -1, 0, 1, -1, 1], -36), ([0, 0, -1, 0, 2, -1, 0], -36), ([0, 0, -1, 1, 1, -1, 0], 36), ([0, 1, -2, 0, 1, 0, 0], -36), ([0, 1, -2, 0, 2, -1, 0], 36), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, -1, 0, 2, -2, 0], -36), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, -1, 1, 1, -1, -1], -36), ([0, 1, 0, 0, 1, -1, -1], -36), ([0, 2, -2, 0, 1, -1, 0], -36), ([1, 0, -1, 0, 2, -1, 0], -36), ([1, 0, -1, 1, 1, -1, 0], 36), ([1, 1, -2, 0, 1, 0, 0], -36), ([1, 1, -2, 0, 2, -1, 0], 36), ([1, 1, -1, -1, 1, -1, 1], 36), ([1, 1, -1, 0, 0, -1, 1], -36), ([1, 1, -1, 0, 1, 0, -1], 36), ([1, 1, -1, 1, 1, -1, -1], -36), ([1, 1, 0, -1, 1, -1, 0], -36), ([1, 1, 0, 0, 1, -2, 0], 36), ([1, 2, -1, 0, 0, -1, 0], 36), ([1, 2, -1, 0, 1, -2, 0], -36)]

theorem source97_checked : normalize (row ![1, -1, 0, 1, -1, 0] ![1, -1, 0, 1, -1, 0] (-12, 0)) = source97 := by
  decide +kernel

theorem source97_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source97 (momentValues f) = 0 := by
  rw [← source97_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source98 : Sparse := [([0, 0, -1, 0, 1, 1, -1], -36), ([0, 0, -1, 0, 2, 0, -1], -36), ([0, 0, -1, 1, 1, 0, -1], -36), ([0, 1, -2, 0, 1, 0, 0], -36), ([0, 1, -2, 0, 2, 0, -1], -36), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, -1, 1, 1, -1], -36), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, -1, 0, 1, -1, 0], -36), ([0, 1, -1, 0, 2, 0, -2], -36), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 1, 1, -1, -1], -36), ([0, 1, 0, -1, 1, 0, -1], -36), ([0, 1, 0, 0, 1, -1, -1], -36), ([0, 1, 0, 0, 1, 0, -2], -36), ([0, 2, -2, 0, 1, 0, -1], -36), ([0, 2, -1, 0, 0, 0, -1], -36), ([0, 2, -1, 0, 1, 0, -2], -36), ([1, 0, -1, 0, 2, 0, -1], -36), ([1, 1, -2, 0, 1, 0, 0], -36), ([1, 1, -1, -1, 1, 1, -1], -36), ([1, 1, -1, 1, 1, -1, -1], -36), ([1, 1, 0, 0, 1, 0, -2], -36), ([1, 2, -1, 0, 0, 0, -1], -36)]

theorem source98_checked : normalize (row ![1, -1, 0, 1, 0, -1] ![1, -1, 0, 1, 0, -1] (-12, 0)) = source98 := by
  decide +kernel

theorem source98_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source98 (momentValues f) = 0 := by
  rw [← source98_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source99 : Sparse := [([0, 0, -1, 1, -1, 0, 1], -36), ([0, 0, -1, 1, -1, 1, 0], -36), ([0, 1, -2, 2, -1, 0, 0], -36), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, -1, 0, -1, 1, 0], -36), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 2, -2, 0, 0], -36), ([0, 1, 0, 1, -1, -1, 0], -36), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 2, -2, 1, -1, 0, 0], -36), ([0, 2, -1, 1, -2, 0, 0], -36), ([1, 0, -1, 2, -1, 0, 0], 36), ([1, 1, -2, 1, 0, 0, 0], 36), ([1, 1, -1, 1, -1, -1, 1], 36), ([1, 1, -1, 1, -1, 1, -1], 36), ([1, 1, 0, 1, -2, 0, 0], 36), ([1, 2, -1, 0, -1, 0, 0], 36)]

theorem source99_checked : normalize (row ![1, -1, 1, -1, 0, 0] ![1, -1, 1, -1, 0, 0] (-12, 0)) = source99 := by
  decide +kernel

theorem source99_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source99 (momentValues f) = 0 := by
  rw [← source99_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source100 : Sparse := [([0, 0, -1, 1, 0, -1, 1], -36), ([0, 0, -1, 1, 1, -1, 0], 36), ([0, 0, -1, 2, 0, -1, 0], -36), ([0, 1, -2, 2, 0, -1, 0], -36), ([0, 1, -1, 0, 1, -1, 0], -36), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 1, 1, -1, -1], -36), ([0, 1, -1, 2, 0, -2, 0], 36), ([0, 1, 0, 1, -1, -1, 0], -36), ([0, 1, 0, 1, 0, -2, 0], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 2, -1, 1, 0, -2, 0], -36), ([1, 0, -1, 1, 1, -1, 0], 36), ([1, 0, -1, 2, 0, -1, 0], -36), ([1, 1, -2, 1, 0, 0, 0], 36), ([1, 1, -1, 0, 0, -1, 1], -36), ([1, 1, -1, 1, -1, -1, 1], 36), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, -1, 1, 1, -1, -1], -36), ([1, 1, -1, 2, 0, -2, 0], 36), ([1, 1, 0, 1, 0, -2, 0], -36), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 2, -2, 1, 0, -1, 0], -36), ([1, 2, -1, 0, 0, -1, 0], 36)]

theorem source100_checked : normalize (row ![1, -1, 1, 0, -1, 0] ![1, -1, 1, 0, -1, 0] (-12, 0)) = source100 := by
  decide +kernel

theorem source100_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source100 (momentValues f) = 0 := by
  rw [← source100_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source101 : Sparse := [([0, 0, -1, 1, 1, 0, -1], -36), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, -1, 1, 1, -1, -1], -36), ([0, 1, -1, 2, 0, 0, -2], -36), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 1, 0, 1, 0, 0, -2], -36), ([0, 2, -2, 1, 0, 0, -1], -36), ([0, 2, -1, 0, 0, 0, -1], -36), ([0, 2, -1, 1, 0, 0, -2], 36), ([1, 0, -1, 1, 0, 1, -1], -36), ([1, 0, -1, 2, 0, 0, -1], 36), ([1, 1, -2, 1, 0, 0, 0], 36), ([1, 1, -2, 2, 0, 0, -1], -36), ([1, 1, -1, 0, 1, 0, -1], 36), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, -1, 1, -1, 1, -1], 36), ([1, 1, -1, 1, 1, -1, -1], -36), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 1, 0, 1, 0, 0, -2], -36), ([1, 2, -1, 0, 0, 0, -1], -36), ([1, 2, -1, 1, 0, 0, -2], 36)]

theorem source101_checked : normalize (row ![1, -1, 1, 0, 0, -1] ![1, -1, 1, 0, 0, -1] (-12, 0)) = source101 := by
  decide +kernel

theorem source101_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source101 (momentValues f) = 0 := by
  rw [← source101_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source102 : Sparse := [([0, 0, 0, -1, -1, 0, 2], -36), ([0, 0, 0, -1, -1, 1, 1], -36), ([0, 0, 1, -1, -1, 0, 1], -36), ([0, 1, -1, -1, -1, 1, 1], -36), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, 0, -2, -1, 0, 2], -36), ([0, 1, 0, -2, 0, 0, 1], -36), ([0, 1, 0, -1, -2, 0, 2], -36), ([0, 1, 0, -1, -1, 1, 0], -36), ([0, 1, 0, -1, 0, -1, 1], -36), ([0, 1, 0, 0, -2, 0, 1], -36), ([0, 1, 0, 0, -1, -1, 1], -36), ([0, 1, 1, -1, -1, -1, 1], -36), ([0, 1, 1, -1, -1, 0, 0], -36), ([0, 2, 0, -2, -1, 0, 1], -36), ([0, 2, 0, -1, -2, 0, 1], -36), ([0, 2, 0, -1, -1, 0, 0], -36), ([1, 0, 0, -1, -1, 0, 2], -36), ([1, 1, -1, -1, -1, 1, 1], -36), ([1, 1, 0, -2, 0, 0, 1], -36), ([1, 1, 0, 0, -2, 0, 1], -36), ([1, 1, 1, -1, -1, -1, 1], -36), ([1, 2, 0, -1, -1, 0, 0], -36)]

theorem source102_checked : normalize (row ![1, 0, -1, -1, 0, 1] ![1, 0, -1, -1, 0, 1] (-12, 0)) = source102 := by
  decide +kernel

theorem source102_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source102 (momentValues f) = 0 := by
  rw [← source102_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source103 : Sparse := [([0, 0, 0, -1, -1, 1, 1], -36), ([0, 1, -1, -1, -1, 1, 1], -36), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, 0, -1, 1, 0], -36), ([0, 1, 0, -2, -1, 2, 0], -36), ([0, 1, 0, -2, 0, 1, 0], -36), ([0, 1, 0, -1, -1, 0, 1], 36), ([0, 1, 0, -1, 0, 1, -1], -36), ([0, 1, 1, -1, -1, 0, 0], -36), ([0, 2, 0, -2, -1, 1, 0], 36), ([0, 2, 0, -1, -2, 1, 0], -36), ([0, 2, 0, -1, -1, 0, 0], -36), ([1, 0, 0, -1, -1, 2, 0], 36), ([1, 0, 1, -1, -1, 1, 0], -36), ([1, 1, -1, -1, -1, 1, 1], -36), ([1, 1, -1, -1, 0, 1, 0], 36), ([1, 1, 0, -2, 0, 1, 0], -36), ([1, 1, 0, -1, -2, 2, 0], -36), ([1, 1, 0, -1, -1, 0, 1], 36), ([1, 1, 0, 0, -2, 1, 0], 36), ([1, 1, 0, 0, -1, 1, -1], -36), ([1, 1, 1, -1, -1, 1, -1], 36), ([1, 2, 0, -2, -1, 1, 0], 36), ([1, 2, 0, -1, -1, 0, 0], -36)]

theorem source103_checked : normalize (row ![1, 0, -1, -1, 1, 0] ![1, 0, -1, -1, 1, 0] (-12, 0)) = source103 := by
  decide +kernel

theorem source103_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source103 (momentValues f) = 0 := by
  rw [← source103_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
