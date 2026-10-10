import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source88 : Sparse := [([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 1, 1, -1, 1, -1], -36), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, 0, 0, 1, -1, 1, -1], -36), ([0, 0, 0, 2, -1, 0, -1], -36), ([0, 0, 1, 0, -1, 1, -1], -36), ([0, 0, 1, 1, -2, 0, 0], -36), ([0, 0, 1, 1, -1, -1, 0], -36), ([0, 0, 1, 1, 0, -1, -1], -36), ([0, 0, 1, 1, 0, 0, -2], -36), ([0, 0, 1, 2, -2, 0, -1], -36), ([0, 0, 1, 2, -1, 0, -2], -36), ([0, 0, 2, 0, -1, 0, -1], -36), ([0, 0, 2, 1, -2, 0, -1], -36), ([0, 0, 2, 1, -1, 0, -2], -36), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 1, 1, -1, -1, -1], -36), ([1, -1, 1, 1, -1, 1, -1], -36), ([1, 0, 0, 2, -1, 0, -1], -36), ([1, 0, 1, 1, -2, 0, 0], -36), ([1, 0, 1, 1, 0, 0, -2], -36), ([1, 0, 2, 0, -1, 0, -1], -36), ([1, 1, 1, 1, -1, -1, -1], -36)]

theorem source88_checked : normalize (row ![0, 1, 1, -1, 0, -1] ![0, 1, 1, -1, 0, -1] (-12, 0)) = source88 := by
  decide +kernel

theorem source88_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source88 (momentValues f) = 0 := by
  rw [← source88_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source89 : Sparse := [([0, -1, 1, 1, 0, 0, -1], -36), ([0, 0, 0, 1, 1, -1, -1], -36), ([0, 0, 0, 2, 0, -1, -1], -36), ([0, 0, 1, 1, -1, -1, 0], -36), ([0, 0, 1, 1, -1, 0, -1], 36), ([0, 0, 1, 1, 0, 0, -2], -36), ([0, 0, 1, 2, 0, -2, -1], -36), ([0, 0, 1, 2, 0, -1, -2], 36), ([0, 0, 2, 1, 0, -1, -2], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 1, 1, -1, -1, -1], -36), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 1, 1, 1, -1, -1], 36), ([1, 0, 0, 2, 0, -1, -1], -36), ([1, 0, 1, 0, 1, -1, -1], -36), ([1, 0, 1, 1, -1, 0, -1], 36), ([1, 0, 1, 1, 0, -2, 0], 36), ([1, 0, 1, 1, 0, 0, -2], -36), ([1, 0, 1, 2, 0, -1, -2], 36), ([1, 0, 2, 0, 0, -1, -1], 36), ([1, 0, 2, 1, 0, -2, -1], -36), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 1, 1, 1, -1, -1, -1], -36)]

theorem source89_checked : normalize (row ![0, 1, 1, 0, -1, -1] ![0, 1, 1, 0, -1, -1] (-12, 0)) = source89 := by
  decide +kernel

theorem source89_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source89 (momentValues f) = 0 := by
  rw [← source89_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source90 : Sparse := [([0, 0, -1, -1, 0, 1, 1], -36), ([0, 1, -1, -2, 0, 0, 2], -36), ([0, 1, -1, -1, -1, 1, 1], -36), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, 0, -2, 0, 0, 1], -36), ([0, 1, 0, -1, -1, 0, 1], 36), ([0, 1, 0, -1, 0, -1, 1], -36), ([0, 2, -2, -1, 0, 0, 1], -36), ([0, 2, -1, -2, 0, 0, 1], 36), ([0, 2, -1, -1, 0, 0, 0], -36), ([1, 0, -1, -1, 0, 0, 2], 36), ([1, 0, -1, -1, 1, 0, 1], -36), ([1, 1, -2, -1, 0, 0, 2], -36), ([1, 1, -2, 0, 0, 0, 1], 36), ([1, 1, -1, -1, -1, 1, 1], -36), ([1, 1, -1, -1, 0, 1, 0], 36), ([1, 1, -1, -1, 1, -1, 1], 36), ([1, 1, -1, 0, 0, -1, 1], -36), ([1, 1, 0, -2, 0, 0, 1], -36), ([1, 1, 0, -1, -1, 0, 1], 36), ([1, 2, -1, -2, 0, 0, 1], 36), ([1, 2, -1, -1, 0, 0, 0], -36)]

theorem source90_checked : normalize (row ![1, -1, -1, 0, 0, 1] ![1, -1, -1, 0, 0, 1] (-12, 0)) = source90 := by
  decide +kernel

theorem source90_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source90 (momentValues f) = 0 := by
  rw [← source90_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source91 : Sparse := [([0, 0, -1, -1, 0, 1, 1], -36), ([0, 0, -1, -1, 0, 2, 0], -36), ([0, 0, -1, -1, 1, 1, 0], -36), ([0, 1, -2, -1, 0, 2, 0], -36), ([0, 1, -2, 0, 0, 1, 0], -36), ([0, 1, -1, -2, 0, 2, 0], -36), ([0, 1, -1, -1, -1, 1, 1], -36), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, -1, 1, 1, -1], -36), ([0, 1, -1, 0, -1, 1, 0], -36), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, 0, -2, 0, 1, 0], -36), ([0, 1, 0, -1, -1, 1, 0], -36), ([0, 1, 0, -1, 0, 1, -1], -36), ([0, 2, -2, -1, 0, 1, 0], -36), ([0, 2, -1, -2, 0, 1, 0], -36), ([0, 2, -1, -1, 0, 0, 0], -36), ([1, 0, -1, -1, 0, 2, 0], -36), ([1, 1, -2, 0, 0, 1, 0], -36), ([1, 1, -1, -1, -1, 1, 1], -36), ([1, 1, -1, -1, 1, 1, -1], -36), ([1, 1, 0, -2, 0, 1, 0], -36), ([1, 2, -1, -1, 0, 0, 0], -36)]

theorem source91_checked : normalize (row ![1, -1, -1, 0, 1, 0] ![1, -1, -1, 0, 1, 0] (-12, 0)) = source91 := by
  decide +kernel

theorem source91_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source91 (momentValues f) = 0 := by
  rw [← source91_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source92 : Sparse := [([0, 0, -1, -1, 1, 1, 0], -36), ([0, 1, -2, -1, 2, 0, 0], -36), ([0, 1, -2, 0, 1, 0, 0], -36), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, -1, 1, 1, -1], -36), ([0, 1, -1, 0, 1, -1, 0], -36), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, 0, -1, 1, 0, -1], -36), ([0, 2, -2, -1, 1, 0, 0], 36), ([0, 2, -1, -2, 1, 0, 0], -36), ([0, 2, -1, -1, 0, 0, 0], -36), ([1, 0, -1, -1, 1, 0, 1], -36), ([1, 0, -1, -1, 2, 0, 0], 36), ([1, 1, -2, 0, 1, 0, 0], -36), ([1, 1, -1, -2, 2, 0, 0], -36), ([1, 1, -1, -1, 0, 1, 0], 36), ([1, 1, -1, -1, 1, -1, 1], 36), ([1, 1, -1, -1, 1, 1, -1], -36), ([1, 1, -1, 0, 1, 0, -1], 36), ([1, 1, 0, -2, 1, 0, 0], 36), ([1, 1, 0, -1, 1, -1, 0], -36), ([1, 2, -2, -1, 1, 0, 0], 36), ([1, 2, -1, -1, 0, 0, 0], -36)]

theorem source92_checked : normalize (row ![1, -1, -1, 1, 0, 0] ![1, -1, -1, 1, 0, 0] (-12, 0)) = source92 := by
  decide +kernel

theorem source92_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source92 (momentValues f) = 0 := by
  rw [← source92_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source93 : Sparse := [([0, 0, -1, 0, -1, 0, 2], -36), ([0, 0, -1, 0, -1, 1, 1], 36), ([0, 0, -1, 1, -1, 0, 1], -36), ([0, 1, -2, 0, -1, 0, 2], -36), ([0, 1, -1, -1, -1, 1, 1], -36), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, -1, 0, -2, 0, 2], 36), ([0, 1, -1, 0, -1, 1, 0], -36), ([0, 1, 0, -1, -1, 0, 1], 36), ([0, 1, 0, 0, -2, 0, 1], -36), ([0, 1, 0, 0, -1, -1, 1], -36), ([0, 2, -1, 0, -2, 0, 1], -36), ([1, 0, -1, 0, -1, 0, 2], -36), ([1, 0, -1, 0, -1, 1, 1], 36), ([1, 1, -2, 0, 0, 0, 1], 36), ([1, 1, -1, -1, -1, 1, 1], -36), ([1, 1, -1, 0, -2, 0, 2], 36), ([1, 1, -1, 0, 0, -1, 1], -36), ([1, 1, -1, 1, -1, -1, 1], 36), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, 0, -1, -1, 0, 1], 36), ([1, 1, 0, 0, -2, 0, 1], -36), ([1, 2, -2, 0, -1, 0, 1], -36), ([1, 2, -1, 0, -1, 0, 0], 36)]

theorem source93_checked : normalize (row ![1, -1, 0, -1, 0, 1] ![1, -1, 0, -1, 0, 1] (-12, 0)) = source93 := by
  decide +kernel

theorem source93_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source93 (momentValues f) = 0 := by
  rw [← source93_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source94 : Sparse := [([0, 0, -1, 0, -1, 1, 1], 36), ([0, 0, -1, 0, -1, 2, 0], -36), ([0, 0, -1, 1, -1, 1, 0], -36), ([0, 1, -2, 0, -1, 2, 0], 36), ([0, 1, -2, 0, 0, 1, 0], -36), ([0, 1, -1, -1, -1, 1, 1], -36), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, 0, -2, 2, 0], -36), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, 0, -1, -1, 1, 0], -36), ([0, 2, -2, 0, -1, 1, 0], -36), ([1, 0, -1, 0, -1, 1, 1], 36), ([1, 0, -1, 0, -1, 2, 0], -36), ([1, 1, -2, 0, -1, 2, 0], 36), ([1, 1, -2, 0, 0, 1, 0], -36), ([1, 1, -1, -1, -1, 1, 1], -36), ([1, 1, -1, -1, 0, 1, 0], 36), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, -1, 1, -1, 1, -1], 36), ([1, 1, 0, 0, -2, 1, 0], 36), ([1, 1, 0, 0, -1, 1, -1], -36), ([1, 2, -1, 0, -2, 1, 0], -36), ([1, 2, -1, 0, -1, 0, 0], 36)]

theorem source94_checked : normalize (row ![1, -1, 0, -1, 1, 0] ![1, -1, 0, -1, 1, 0] (-12, 0)) = source94 := by
  decide +kernel

theorem source94_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source94 (momentValues f) = 0 := by
  rw [← source94_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source95 : Sparse := [([0, 0, -1, 0, 1, -1, 1], -36), ([0, 0, -1, 1, 0, -1, 1], -36), ([0, 1, -2, 0, 0, -1, 2], -36), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, -1, 0, 0, -2, 2], -36), ([0, 1, -1, 0, 1, -1, 0], -36), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, 0, -1, 0, -1, 1], -36), ([0, 1, 0, 0, -1, -1, 1], -36), ([0, 2, -2, 0, 0, -1, 1], -36), ([0, 2, -1, 0, 0, -2, 1], -36), ([1, 0, -1, 0, 0, -1, 2], 36), ([1, 1, -2, 0, 0, 0, 1], 36), ([1, 1, -1, -1, 1, -1, 1], 36), ([1, 1, -1, 1, -1, -1, 1], 36), ([1, 1, 0, 0, 0, -2, 1], 36), ([1, 2, -1, 0, 0, -1, 0], 36)]

theorem source95_checked : normalize (row ![1, -1, 0, 0, -1, 1] ![1, -1, 0, 0, -1, 1] (-12, 0)) = source95 := by
  decide +kernel

theorem source95_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source95 (momentValues f) = 0 := by
  rw [← source95_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
