import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source64 : Sparse := [([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, -1, 1, 1, -1, 1], -36), ([0, -1, 0, 0, 1, -1, 1], 36), ([0, 0, -2, 0, 2, -1, 1], -36), ([0, 0, -1, 0, 1, -2, 2], -36), ([0, 0, -1, 0, 2, -2, 1], 36), ([0, 0, -1, 0, 2, -1, 0], -36), ([0, 0, -1, 1, 0, -1, 1], -36), ([0, 0, -1, 1, 1, -1, 0], 36), ([0, 0, 0, -1, 1, -1, 1], -36), ([0, 0, 0, 0, 1, -2, 1], -36), ([0, 1, -1, 0, 1, -1, 0], -36), ([1, -1, -1, 1, 1, -1, 1], -36), ([1, -1, 0, 0, 1, -1, 1], 36), ([1, 0, -2, 0, 1, -1, 2], -36), ([1, 0, -2, 0, 1, 0, 1], 36), ([1, 0, -1, -1, 1, 0, 1], -36), ([1, 0, -1, 0, 0, -1, 2], 36), ([1, 0, -1, 0, 2, -2, 1], 36), ([1, 0, -1, 0, 2, -1, 0], -36), ([1, 0, -1, 1, 1, -1, 0], 36), ([1, 0, 0, 0, 1, -2, 1], -36), ([1, 1, -1, -1, 1, -1, 1], 36), ([1, 1, -1, 0, 0, -1, 1], -36)]

theorem source64_checked : normalize (row ![0, -1, 0, 1, -1, 1] ![0, -1, 0, 1, -1, 1] (-12, 0)) = source64 := by
  decide +kernel

theorem source64_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source64 (momentValues f) = 0 := by
  rw [← source64_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source65 : Sparse := [([0, -1, 0, 0, 1, 1, -1], -36), ([0, 0, -2, 0, 2, 1, -1], -36), ([0, 0, -1, -1, 1, 1, 0], -36), ([0, 0, -1, 0, 1, 2, -2], -36), ([0, 0, -1, 0, 2, 0, -1], -36), ([0, 0, -1, 0, 2, 1, -2], 36), ([0, 0, -1, 1, 1, 0, -1], -36), ([0, 0, 0, -1, 1, 1, -1], 36), ([0, 0, 0, 0, 1, 1, -2], -36), ([0, 1, -1, -1, 1, 1, -1], -36), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, -1, 0, 1, 0, -1], 36), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, -1, -1, 1, 1, 1, -1], 36), ([1, 0, -2, 0, 1, 1, 0], 36), ([1, 0, -2, 0, 1, 2, -1], -36), ([1, 0, -1, 0, 0, 2, -1], 36), ([1, 0, -1, 0, 2, 0, -1], -36), ([1, 0, -1, 0, 2, 1, -2], 36), ([1, 0, -1, 1, 0, 1, -1], -36), ([1, 0, 0, -1, 1, 1, -1], 36), ([1, 0, 0, 0, 1, 1, -2], -36), ([1, 1, -1, -1, 1, 1, -1], -36), ([1, 1, -1, 0, 1, 0, -1], 36)]

theorem source65_checked : normalize (row ![0, -1, 0, 1, 1, -1] ![0, -1, 0, 1, 1, -1] (-12, 0)) = source65 := by
  decide +kernel

theorem source65_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source65 (momentValues f) = 0 := by
  rw [← source65_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source66 : Sparse := [([0, -1, -1, 1, -1, 1, 1], -36), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, 0, 1, -1, 0, 1], -36), ([0, 0, -2, 1, -1, 0, 2], 36), ([0, 0, -2, 1, 0, 0, 1], -36), ([0, 0, -2, 2, -1, 0, 1], -36), ([0, 0, -1, 0, -1, 0, 2], -36), ([0, 0, -1, 0, -1, 1, 1], 36), ([0, 0, -1, 1, -2, 0, 2], -36), ([0, 0, -1, 1, -1, 1, 0], -36), ([0, 0, -1, 1, 0, -1, 1], -36), ([0, 1, -1, 0, -1, 0, 1], -36), ([1, -1, -1, 1, -1, 1, 1], -36), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, 0, -2, 1, -1, 0, 2], 36), ([1, 0, -2, 1, 0, 0, 1], -36), ([1, 0, -1, 0, -1, 0, 2], -36), ([1, 0, -1, 0, -1, 1, 1], 36), ([1, 0, -1, 2, -2, 0, 1], -36), ([1, 0, -1, 2, -1, 0, 0], 36), ([1, 0, 0, 1, -2, 0, 1], 36), ([1, 0, 0, 1, -1, -1, 1], -36), ([1, 1, -1, 1, -1, -1, 1], 36), ([1, 1, -1, 1, -1, 0, 0], -36)]

theorem source66_checked : normalize (row ![0, -1, 1, -1, 0, 1] ![0, -1, 1, -1, 0, 1] (-12, 0)) = source66 := by
  decide +kernel

theorem source66_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source66 (momentValues f) = 0 := by
  rw [← source66_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source67 : Sparse := [([0, -1, -1, 1, -1, 1, 1], -36), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, 0, 1, -1, 1, 0], 36), ([0, 0, -2, 1, -1, 2, 0], -36), ([0, 0, -1, 0, -1, 1, 1], 36), ([0, 0, -1, 0, -1, 2, 0], -36), ([0, 0, -1, 1, -2, 2, 0], 36), ([0, 0, -1, 1, -1, 0, 1], -36), ([0, 0, -1, 2, -2, 1, 0], -36), ([0, 0, 0, 1, -2, 1, 0], -36), ([0, 0, 0, 1, -1, 1, -1], -36), ([0, 1, -1, 0, -1, 1, 0], -36), ([1, -1, -1, 1, -1, 1, 1], -36), ([1, -1, 0, 1, -1, 1, 0], 36), ([1, 0, -2, 1, 0, 1, 0], 36), ([1, 0, -2, 2, -1, 1, 0], -36), ([1, 0, -1, 0, -1, 1, 1], 36), ([1, 0, -1, 0, -1, 2, 0], -36), ([1, 0, -1, 1, -2, 2, 0], 36), ([1, 0, -1, 1, 0, 1, -1], -36), ([1, 0, -1, 2, -1, 0, 0], 36), ([1, 0, 0, 1, -2, 1, 0], -36), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, -1, 1, -1, 1, -1], 36)]

theorem source67_checked : normalize (row ![0, -1, 1, -1, 1, 0] ![0, -1, 1, -1, 1, 0] (-12, 0)) = source67 := by
  decide +kernel

theorem source67_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source67 (momentValues f) = 0 := by
  rw [← source67_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source68 : Sparse := [([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 1, 1, -1, 1], -36), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, 0, -2, 1, 0, -1, 2], -36), ([0, 0, -2, 1, 0, 0, 1], -36), ([0, 0, -2, 2, 0, -1, 1], 36), ([0, 0, -1, 0, 1, -1, 1], -36), ([0, 0, -1, 1, -1, 0, 1], -36), ([0, 0, -1, 1, 1, -1, 0], 36), ([0, 0, -1, 2, 0, -2, 1], -36), ([0, 0, -1, 2, 0, -1, 0], -36), ([0, 1, -1, 1, 0, -1, 0], -36), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 1, 1, -1, 1], -36), ([1, 0, -2, 1, 0, 0, 1], -36), ([1, 0, -2, 2, 0, -1, 1], 36), ([1, 0, -1, 0, 0, -1, 2], 36), ([1, 0, -1, 1, 0, -2, 2], -36), ([1, 0, -1, 1, 1, -1, 0], 36), ([1, 0, -1, 2, 0, -1, 0], -36), ([1, 0, 0, 1, -1, -1, 1], -36), ([1, 0, 0, 1, 0, -2, 1], 36), ([1, 1, -1, 0, 0, -1, 1], -36), ([1, 1, -1, 1, -1, -1, 1], 36)]

theorem source68_checked : normalize (row ![0, -1, 1, 0, -1, 1] ![0, -1, 1, 0, -1, 1] (-12, 0)) = source68 := by
  decide +kernel

theorem source68_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source68 (momentValues f) = 0 := by
  rw [← source68_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source69 : Sparse := [([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, 0, 1, 0, 1, -1], -36), ([0, 0, -2, 1, 0, 2, -1], -36), ([0, 0, -2, 2, 0, 1, -1], -36), ([0, 0, -1, 0, 1, 1, -1], -36), ([0, 0, -1, 1, -1, 1, 0], -36), ([0, 0, -1, 1, 0, 2, -2], -36), ([0, 0, -1, 1, 1, 0, -1], -36), ([0, 0, -1, 2, 0, 1, -2], -36), ([0, 0, 0, 1, -1, 1, -1], -36), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, -1, 1, 0, 0, -1], -36), ([1, -1, -1, 1, 1, 1, -1], 36), ([1, 0, -2, 1, 0, 1, 0], 36), ([1, 0, -1, 0, 0, 2, -1], 36), ([1, 0, -1, 2, 0, 0, -1], 36), ([1, 0, 0, 1, 0, 1, -2], 36), ([1, 1, -1, 1, -1, 1, -1], 36)]

theorem source69_checked : normalize (row ![0, -1, 1, 0, 1, -1] ![0, -1, 1, 0, 1, -1] (-12, 0)) = source69 := by
  decide +kernel

theorem source69_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source69 (momentValues f) = 0 := by
  rw [← source69_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source70 : Sparse := [([0, -1, -1, 1, 1, -1, 1], -36), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, 0, 1, 1, -1, 0], -36), ([0, 0, -2, 1, 1, 0, 0], -36), ([0, 0, -2, 1, 2, -1, 0], -36), ([0, 0, -2, 2, 1, -1, 0], -36), ([0, 0, -1, 0, 1, -1, 1], -36), ([0, 0, -1, 0, 2, -1, 0], -36), ([0, 0, -1, 1, 0, -1, 1], -36), ([0, 0, -1, 1, 1, 0, -1], -36), ([0, 0, -1, 1, 2, -2, 0], -36), ([0, 0, -1, 2, 0, -1, 0], -36), ([0, 0, -1, 2, 1, -2, 0], -36), ([0, 0, 0, 1, 1, -2, 0], -36), ([0, 0, 0, 1, 1, -1, -1], -36), ([0, 1, -1, 0, 1, -1, 0], -36), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, -1, 1, 1, -1, -1], -36), ([1, -1, -1, 1, 1, -1, 1], -36), ([1, 0, -2, 1, 1, 0, 0], -36), ([1, 0, -1, 0, 2, -1, 0], -36), ([1, 0, -1, 2, 0, -1, 0], -36), ([1, 0, 0, 1, 1, -2, 0], -36), ([1, 1, -1, 1, 1, -1, -1], -36)]

theorem source70_checked : normalize (row ![0, -1, 1, 1, -1, 0] ![0, -1, 1, 1, -1, 0] (-12, 0)) = source70 := by
  decide +kernel

theorem source70_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source70 (momentValues f) = 0 := by
  rw [← source70_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source71 : Sparse := [([0, -1, -1, 1, 1, 0, 0], -36), ([0, 0, -2, 1, 1, 0, 0], -36), ([0, 0, -2, 1, 2, 0, -1], 36), ([0, 0, -2, 2, 1, 0, -1], -36), ([0, 0, -1, 0, 1, 1, -1], -36), ([0, 0, -1, 0, 2, 0, -1], -36), ([0, 0, -1, 1, 1, -1, 0], 36), ([0, 0, -1, 1, 2, 0, -2], -36), ([0, 0, 0, 1, 1, -1, -1], -36), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 1, 1, -1, -1], -36), ([1, -1, -1, 1, 1, 1, -1], 36), ([1, -1, 0, 1, 1, 0, -1], -36), ([1, 0, -2, 1, 1, 0, 0], -36), ([1, 0, -2, 1, 2, 0, -1], 36), ([1, 0, -1, 0, 2, 0, -1], -36), ([1, 0, -1, 1, 0, 1, -1], -36), ([1, 0, -1, 1, 1, -1, 0], 36), ([1, 0, -1, 2, 0, 0, -1], 36), ([1, 0, -1, 2, 1, 0, -2], -36), ([1, 0, 0, 1, 1, 0, -2], 36), ([1, 1, -1, 0, 1, 0, -1], 36), ([1, 1, -1, 1, 1, -1, -1], -36)]

theorem source71_checked : normalize (row ![0, -1, 1, 1, 0, -1] ![0, -1, 1, 1, 0, -1] (-12, 0)) = source71 := by
  decide +kernel

theorem source71_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source71 (momentValues f) = 0 := by
  rw [← source71_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
