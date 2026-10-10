import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source72 : Sparse := [([0, -1, 0, 0, -1, 1, 1], -36), ([0, 0, -1, -1, 0, 1, 1], -36), ([0, 0, -1, 0, -1, 1, 1], 36), ([0, 0, 0, -2, -1, 1, 2], -36), ([0, 0, 0, -1, -2, 1, 2], 36), ([0, 0, 0, -1, -2, 2, 1], -36), ([0, 0, 0, -1, -1, 0, 2], -36), ([0, 0, 0, 0, -2, 1, 1], -36), ([0, 0, 1, -1, -1, 0, 1], -36), ([0, 1, -1, -1, -1, 1, 1], -36), ([0, 1, 0, -1, -1, 0, 1], 36), ([0, 1, 0, -1, -1, 1, 0], -36), ([1, -1, 0, -1, 0, 1, 1], -36), ([1, -1, 1, -1, -1, 1, 1], 36), ([1, 0, -1, 0, -1, 1, 1], 36), ([1, 0, 0, -2, -1, 2, 1], -36), ([1, 0, 0, -2, 0, 1, 1], 36), ([1, 0, 0, -1, -2, 1, 2], 36), ([1, 0, 0, -1, -1, 0, 2], -36), ([1, 0, 0, -1, -1, 2, 0], 36), ([1, 0, 0, 0, -2, 1, 1], -36), ([1, 0, 1, -1, -1, 1, 0], -36), ([1, 1, -1, -1, -1, 1, 1], -36), ([1, 1, 0, -1, -1, 0, 1], 36)]

theorem source72_checked : normalize (row ![0, 0, -1, -1, 1, 1] ![0, 0, -1, -1, 1, 1] (-12, 0)) = source72 := by
  decide +kernel

theorem source72_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source72 (momentValues f) = 0 := by
  rw [← source72_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source73 : Sparse := [([0, -1, 0, -1, 1, 0, 1], -36), ([0, -1, 0, 0, 1, -1, 1], 36), ([0, -1, 1, -1, 1, -1, 1], -36), ([0, 0, -1, 0, 1, -1, 1], -36), ([0, 0, 0, -2, 1, -1, 2], -36), ([0, 0, 0, -1, 0, -1, 2], -36), ([0, 0, 0, -1, 1, -2, 2], 36), ([0, 0, 0, -1, 2, -2, 1], -36), ([0, 0, 0, 0, 1, -2, 1], -36), ([0, 0, 1, -1, 0, -1, 1], 36), ([0, 0, 1, -1, 1, -1, 0], -36), ([0, 1, 0, -1, 0, -1, 1], -36), ([1, -1, 0, 0, 1, -1, 1], 36), ([1, -1, 1, -1, 1, -1, 1], -36), ([1, 0, -1, -1, 1, 0, 1], -36), ([1, 0, 0, -2, 1, 0, 1], 36), ([1, 0, 0, -2, 2, -1, 1], -36), ([1, 0, 0, -1, 0, -1, 2], -36), ([1, 0, 0, -1, 1, -2, 2], 36), ([1, 0, 0, -1, 2, -1, 0], 36), ([1, 0, 0, 0, 1, -2, 1], -36), ([1, 0, 1, -1, 0, -1, 1], 36), ([1, 1, -1, -1, 1, -1, 1], 36), ([1, 1, 0, -1, 1, -1, 0], -36)]

theorem source73_checked : normalize (row ![0, 0, -1, 1, -1, 1] ![0, 0, -1, 1, -1, 1] (-12, 0)) = source73 := by
  decide +kernel

theorem source73_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source73 (momentValues f) = 0 := by
  rw [← source73_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source74 : Sparse := [([0, -1, 0, -1, 1, 1, 0], -36), ([0, -1, 0, 0, 1, 1, -1], -36), ([0, -1, 1, -1, 1, 1, -1], -36), ([0, 0, -1, -1, 1, 1, 0], -36), ([0, 0, -1, 0, 1, 1, -1], -36), ([0, 0, 0, -2, 1, 1, 0], -36), ([0, 0, 0, -2, 1, 2, -1], -36), ([0, 0, 0, -2, 2, 1, -1], -36), ([0, 0, 0, -1, 0, 2, -1], -36), ([0, 0, 0, -1, 1, 2, -2], -36), ([0, 0, 0, -1, 2, 0, -1], -36), ([0, 0, 0, -1, 2, 1, -2], -36), ([0, 0, 0, 0, 1, 1, -2], -36), ([0, 0, 1, -1, 0, 1, -1], -36), ([0, 0, 1, -1, 1, 0, -1], -36), ([0, 1, -1, -1, 1, 1, -1], -36), ([0, 1, 0, -1, 0, 1, -1], -36), ([0, 1, 0, -1, 1, 0, -1], -36), ([1, -1, 1, -1, 1, 1, -1], -36), ([1, 0, 0, -2, 1, 1, 0], -36), ([1, 0, 0, -1, 0, 2, -1], -36), ([1, 0, 0, -1, 2, 0, -1], -36), ([1, 0, 0, 0, 1, 1, -2], -36), ([1, 1, -1, -1, 1, 1, -1], -36)]

theorem source74_checked : normalize (row ![0, 0, -1, 1, 1, -1] ![0, 0, -1, 1, 1, -1] (-12, 0)) = source74 := by
  decide +kernel

theorem source74_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source74 (momentValues f) = 0 := by
  rw [← source74_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source75 : Sparse := [([0, -1, 0, 1, -1, 0, 1], -36), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, 0, -1, 1, -1, 0, 1], -36), ([0, 0, -1, 1, 0, -1, 1], -36), ([0, 0, 0, 1, -2, -1, 2], -36), ([0, 0, 0, 1, -1, -2, 2], -36), ([0, 0, 0, 2, -2, -1, 1], -36), ([0, 0, 0, 2, -1, -2, 1], -36), ([0, 0, 1, 0, -1, -1, 1], -36), ([0, 0, 1, 1, -1, -1, 0], -36), ([0, 1, 0, 0, -1, -1, 1], -36), ([0, 1, 0, 1, -1, -1, 0], -36), ([1, -1, 1, 1, -1, -1, 1], 36), ([1, 0, 0, 0, -1, -1, 2], 36), ([1, 0, 0, 1, -2, 0, 1], 36), ([1, 0, 0, 1, 0, -2, 1], 36), ([1, 0, 0, 2, -1, -1, 0], 36), ([1, 1, -1, 1, -1, -1, 1], 36)]

theorem source75_checked : normalize (row ![0, 0, 1, -1, -1, 1] ![0, 0, 1, -1, -1, 1] (-12, 0)) = source75 := by
  decide +kernel

theorem source75_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source75 (momentValues f) = 0 := by
  rw [← source75_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source76 : Sparse := [([0, -1, 0, 1, -1, 1, 0], 36), ([0, -1, 0, 1, 0, 1, -1], -36), ([0, -1, 1, 1, -1, 1, -1], -36), ([0, 0, -1, 1, -1, 1, 0], -36), ([0, 0, 0, 1, -2, 1, 0], -36), ([0, 0, 0, 1, -2, 2, -1], -36), ([0, 0, 0, 2, -2, 1, -1], 36), ([0, 0, 0, 2, -1, 0, -1], -36), ([0, 0, 0, 2, -1, 1, -2], -36), ([0, 0, 1, 0, -1, 1, -1], -36), ([0, 0, 1, 1, -1, 0, -1], 36), ([0, 1, 0, 1, -1, 0, -1], -36), ([1, -1, 0, 1, -1, 1, 0], 36), ([1, -1, 1, 1, -1, 1, -1], -36), ([1, 0, -1, 1, 0, 1, -1], -36), ([1, 0, 0, 0, -1, 2, -1], 36), ([1, 0, 0, 1, -2, 1, 0], -36), ([1, 0, 0, 1, -1, 2, -2], -36), ([1, 0, 0, 1, 0, 1, -2], 36), ([1, 0, 0, 2, -2, 1, -1], 36), ([1, 0, 0, 2, -1, 0, -1], -36), ([1, 0, 1, 1, -1, 0, -1], 36), ([1, 1, -1, 1, -1, 1, -1], 36), ([1, 1, 0, 0, -1, 1, -1], -36)]

theorem source76_checked : normalize (row ![0, 0, 1, -1, 1, -1] ![0, 0, 1, -1, 1, -1] (-12, 0)) = source76 := by
  decide +kernel

theorem source76_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source76 (momentValues f) = 0 := by
  rw [← source76_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source77 : Sparse := [([0, -1, 0, 1, 1, -1, 0], -36), ([0, 0, -1, 1, 1, -1, 0], 36), ([0, 0, -1, 1, 1, 0, -1], -36), ([0, 0, 0, 1, 1, -2, 0], -36), ([0, 0, 0, 1, 2, -2, -1], -36), ([0, 0, 0, 2, 0, -1, -1], -36), ([0, 0, 0, 2, 1, -2, -1], 36), ([0, 0, 0, 2, 1, -1, -2], -36), ([0, 0, 1, 1, 0, -1, -1], -36), ([0, 1, -1, 1, 1, -1, -1], -36), ([0, 1, 0, 0, 1, -1, -1], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([1, -1, 0, 1, 1, 0, -1], -36), ([1, -1, 1, 1, 1, -1, -1], 36), ([1, 0, -1, 1, 1, -1, 0], 36), ([1, 0, 0, 0, 2, -1, -1], 36), ([1, 0, 0, 1, 1, -2, 0], -36), ([1, 0, 0, 1, 1, 0, -2], 36), ([1, 0, 0, 1, 2, -1, -2], -36), ([1, 0, 0, 2, 0, -1, -1], -36), ([1, 0, 0, 2, 1, -2, -1], 36), ([1, 0, 1, 0, 1, -1, -1], -36), ([1, 1, -1, 1, 1, -1, -1], -36), ([1, 1, 0, 1, 0, -1, -1], 36)]

theorem source77_checked : normalize (row ![0, 0, 1, 1, -1, -1] ![0, 0, 1, 1, -1, -1] (-12, 0)) = source77 := by
  decide +kernel

theorem source77_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source77 (momentValues f) = 0 := by
  rw [← source77_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source78 : Sparse := [([0, -1, 1, -1, 0, 0, 1], -36), ([0, 0, 0, -1, -1, 0, 2], -36), ([0, 0, 0, -1, -1, 1, 1], -36), ([0, 0, 1, -2, -1, 0, 2], 36), ([0, 0, 1, -2, 0, 0, 1], -36), ([0, 0, 1, -1, -2, 0, 2], -36), ([0, 0, 1, -1, 0, -1, 1], 36), ([0, 0, 1, 0, -1, -1, 1], -36), ([0, 0, 2, -2, -1, 0, 1], -36), ([0, 1, 0, -1, -1, 0, 1], 36), ([0, 1, 1, -1, -1, -1, 1], -36), ([0, 1, 1, -1, -1, 0, 0], -36), ([1, -1, 1, -1, -1, 1, 1], 36), ([1, -1, 1, 0, -1, 0, 1], -36), ([1, 0, 0, -1, -1, 0, 2], -36), ([1, 0, 1, -2, -1, 0, 2], 36), ([1, 0, 1, -2, 0, 0, 1], -36), ([1, 0, 1, -1, -1, 1, 0], -36), ([1, 0, 1, -1, 0, -1, 1], 36), ([1, 0, 1, 0, -2, 0, 1], 36), ([1, 0, 2, -1, -2, 0, 1], -36), ([1, 0, 2, -1, -1, 0, 0], 36), ([1, 1, 0, -1, -1, 0, 1], 36), ([1, 1, 1, -1, -1, -1, 1], -36)]

theorem source78_checked : normalize (row ![0, 1, -1, -1, 0, 1] ![0, 1, -1, -1, 0, 1] (-12, 0)) = source78 := by
  decide +kernel

theorem source78_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source78 (momentValues f) = 0 := by
  rw [← source78_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source79 : Sparse := [([0, -1, 1, -1, 0, 1, 0], -36), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, 0, 0, -1, -1, 1, 1], -36), ([0, 0, 1, -2, -1, 2, 0], -36), ([0, 0, 1, -1, -2, 2, 0], -36), ([0, 0, 1, -1, -1, 0, 1], -36), ([0, 0, 1, -1, 0, 1, -1], -36), ([0, 0, 1, 0, -1, 1, -1], -36), ([0, 0, 2, -2, -1, 1, 0], -36), ([0, 0, 2, -1, -2, 1, 0], -36), ([0, 1, 0, -1, -1, 1, 0], -36), ([0, 1, 1, -1, -1, 0, 0], -36), ([1, -1, 1, -1, -1, 1, 1], 36), ([1, 0, 0, -1, -1, 2, 0], 36), ([1, 0, 1, -2, 0, 1, 0], 36), ([1, 0, 1, 0, -2, 1, 0], 36), ([1, 0, 2, -1, -1, 0, 0], 36), ([1, 1, 1, -1, -1, 1, -1], 36)]

theorem source79_checked : normalize (row ![0, 1, -1, -1, 1, 0] ![0, 1, -1, -1, 1, 0] (-12, 0)) = source79 := by
  decide +kernel

theorem source79_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source79 (momentValues f) = 0 := by
  rw [← source79_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
