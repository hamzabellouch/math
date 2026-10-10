import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source80 : Sparse := [([0, -1, 1, -1, 0, 0, 1], -36), ([0, -1, 1, -1, 1, -1, 1], -36), ([0, -1, 1, 0, 0, -1, 1], -36), ([0, 0, 0, -1, 0, -1, 2], -36), ([0, 0, 0, -1, 1, -1, 1], -36), ([0, 0, 1, -2, 0, -1, 2], -36), ([0, 0, 1, -2, 0, 0, 1], -36), ([0, 0, 1, -1, -1, 0, 1], -36), ([0, 0, 1, -1, 0, -2, 2], -36), ([0, 0, 1, -1, 1, -1, 0], -36), ([0, 0, 1, 0, -1, -1, 1], -36), ([0, 0, 1, 0, 0, -2, 1], -36), ([0, 0, 2, -2, 0, -1, 1], -36), ([0, 0, 2, -1, 0, -2, 1], -36), ([0, 0, 2, -1, 0, -1, 0], -36), ([0, 1, 0, -1, 0, -1, 1], -36), ([0, 1, 1, -1, -1, -1, 1], -36), ([0, 1, 1, -1, 0, -1, 0], -36), ([1, -1, 1, -1, 1, -1, 1], -36), ([1, 0, 0, -1, 0, -1, 2], -36), ([1, 0, 1, -2, 0, 0, 1], -36), ([1, 0, 1, 0, 0, -2, 1], -36), ([1, 0, 2, -1, 0, -1, 0], -36), ([1, 1, 1, -1, -1, -1, 1], -36)]

theorem source80_checked : normalize (row ![0, 1, -1, 0, -1, 1] ![0, 1, -1, 0, -1, 1] (-12, 0)) = source80 := by
  decide +kernel

theorem source80_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source80 (momentValues f) = 0 := by
  rw [← source80_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source81 : Sparse := [([0, -1, 1, -1, 0, 1, 0], -36), ([0, -1, 1, -1, 1, 1, -1], -36), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, 0, 0, -1, 0, 2, -1], -36), ([0, 0, 0, -1, 1, 1, -1], 36), ([0, 0, 1, -2, 0, 2, -1], -36), ([0, 0, 1, -1, 0, 2, -2], 36), ([0, 0, 1, -1, 1, 0, -1], -36), ([0, 0, 1, 0, -1, 1, -1], -36), ([0, 0, 1, 0, 0, 1, -2], -36), ([0, 0, 2, -1, 0, 1, -2], -36), ([0, 1, 0, -1, 0, 1, -1], -36), ([1, -1, 1, -1, 1, 1, -1], -36), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, 0, 0, -1, 0, 2, -1], -36), ([1, 0, 0, -1, 1, 1, -1], 36), ([1, 0, 1, -2, 0, 1, 0], 36), ([1, 0, 1, -1, -1, 1, 0], -36), ([1, 0, 1, -1, 0, 2, -2], 36), ([1, 0, 1, 0, 0, 1, -2], -36), ([1, 0, 2, -2, 0, 1, -1], -36), ([1, 0, 2, -1, 0, 0, -1], 36), ([1, 1, 1, -1, -1, 1, -1], 36), ([1, 1, 1, -1, 0, 0, -1], -36)]

theorem source81_checked : normalize (row ![0, 1, -1, 0, 1, -1] ![0, 1, -1, 0, 1, -1] (-12, 0)) = source81 := by
  decide +kernel

theorem source81_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source81 (momentValues f) = 0 := by
  rw [← source81_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source82 : Sparse := [([0, -1, 1, -1, 1, -1, 1], -36), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, 0, 1, -1, 0], -36), ([0, 0, 0, -1, 1, -1, 1], -36), ([0, 0, 1, -2, 1, 0, 0], -36), ([0, 0, 1, -2, 2, -1, 0], -36), ([0, 0, 1, -1, 0, -1, 1], 36), ([0, 0, 1, -1, 1, 0, -1], -36), ([0, 0, 2, -2, 1, -1, 0], 36), ([0, 0, 2, -1, 0, -1, 0], -36), ([0, 0, 2, -1, 1, -2, 0], -36), ([0, 1, 1, -1, 0, -1, 0], -36), ([1, -1, 1, -1, 1, -1, 1], -36), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, 0, 0, -1, 2, -1, 0], 36), ([1, 0, 1, -2, 1, 0, 0], -36), ([1, 0, 1, -1, 0, -1, 1], 36), ([1, 0, 1, -1, 2, -2, 0], -36), ([1, 0, 1, 0, 1, -2, 0], 36), ([1, 0, 1, 0, 1, -1, -1], -36), ([1, 0, 2, -2, 1, -1, 0], 36), ([1, 0, 2, -1, 0, -1, 0], -36), ([1, 1, 0, -1, 1, -1, 0], -36), ([1, 1, 1, -1, 1, -1, -1], 36)]

theorem source82_checked : normalize (row ![0, 1, -1, 1, -1, 0] ![0, 1, -1, 1, -1, 0] (-12, 0)) = source82 := by
  decide +kernel

theorem source82_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source82 (momentValues f) = 0 := by
  rw [← source82_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source83 : Sparse := [([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, -1, 1, 1, -1], -36), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, 0, 0, -1, 1, 1, -1], 36), ([0, 0, 0, -1, 2, 0, -1], -36), ([0, 0, 1, -2, 1, 0, 0], -36), ([0, 0, 1, -2, 2, 0, -1], 36), ([0, 0, 1, -1, 0, 1, -1], -36), ([0, 0, 1, -1, 1, -1, 0], -36), ([0, 0, 1, -1, 2, 0, -2], -36), ([0, 0, 2, -2, 1, 0, -1], -36), ([0, 1, 0, -1, 1, 0, -1], -36), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, -1, 1, 1, -1], -36), ([1, 0, 0, -1, 1, 1, -1], 36), ([1, 0, 0, -1, 2, 0, -1], -36), ([1, 0, 1, -2, 1, 0, 0], -36), ([1, 0, 1, -2, 2, 0, -1], 36), ([1, 0, 1, 0, 1, -1, -1], -36), ([1, 0, 1, 0, 1, 0, -2], 36), ([1, 0, 2, -1, 0, 0, -1], 36), ([1, 0, 2, -1, 1, 0, -2], -36), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, -1, 1, -1, -1], 36)]

theorem source83_checked : normalize (row ![0, 1, -1, 1, 0, -1] ![0, 1, -1, 1, 0, -1] (-12, 0)) = source83 := by
  decide +kernel

theorem source83_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source83 (momentValues f) = 0 := by
  rw [← source83_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source84 : Sparse := [([0, -1, 1, 0, 0, -1, 1], -36), ([0, 0, 1, -1, -1, 0, 1], -36), ([0, 0, 1, -1, 0, -1, 1], 36), ([0, 0, 1, 0, -1, -2, 2], -36), ([0, 0, 1, 0, 0, -2, 1], -36), ([0, 0, 1, 1, -1, -1, 0], -36), ([0, 0, 2, 0, -2, -1, 1], -36), ([0, 0, 2, 0, -1, -2, 1], 36), ([0, 0, 2, 0, -1, -1, 0], -36), ([0, 1, 0, 0, -1, -1, 1], -36), ([0, 1, 1, -1, -1, -1, 1], -36), ([0, 1, 1, 0, -1, -1, 0], 36), ([1, -1, 1, 0, -1, 0, 1], -36), ([1, -1, 1, 1, -1, -1, 1], 36), ([1, 0, 0, 0, -1, -1, 2], 36), ([1, 0, 0, 1, -1, -1, 1], -36), ([1, 0, 1, -1, 0, -1, 1], 36), ([1, 0, 1, 0, -2, -1, 2], -36), ([1, 0, 1, 0, -2, 0, 1], 36), ([1, 0, 1, 0, 0, -2, 1], -36), ([1, 0, 2, 0, -1, -2, 1], 36), ([1, 0, 2, 0, -1, -1, 0], -36), ([1, 1, 1, -1, -1, -1, 1], -36), ([1, 1, 1, 0, -1, -1, 0], 36)]

theorem source84_checked : normalize (row ![0, 1, 0, -1, -1, 1] ![0, 1, 0, -1, -1, 1] (-12, 0)) = source84 := by
  decide +kernel

theorem source84_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source84 (momentValues f) = 0 := by
  rw [← source84_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source85 : Sparse := [([0, -1, 1, 0, -1, 1, 0], -36), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, -1, 1, 1, -1, 1, -1], -36), ([0, 0, 0, 1, -1, 1, -1], -36), ([0, 0, 1, -1, 0, 1, -1], -36), ([0, 0, 1, 0, -1, 2, -2], -36), ([0, 0, 1, 0, 0, 1, -2], -36), ([0, 0, 1, 1, -1, 0, -1], 36), ([0, 0, 2, 0, -2, 1, -1], -36), ([0, 0, 2, 0, -1, 0, -1], -36), ([0, 0, 2, 0, -1, 1, -2], 36), ([0, 1, 1, 0, -1, 0, -1], -36), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, -1, 1, 1, -1, 1, -1], -36), ([1, 0, 0, 0, -1, 2, -1], 36), ([1, 0, 1, -1, -1, 1, 0], -36), ([1, 0, 1, 0, -2, 1, 0], 36), ([1, 0, 1, 0, -2, 2, -1], -36), ([1, 0, 1, 0, 0, 1, -2], -36), ([1, 0, 1, 1, -1, 0, -1], 36), ([1, 0, 2, 0, -1, 0, -1], -36), ([1, 0, 2, 0, -1, 1, -2], 36), ([1, 1, 0, 0, -1, 1, -1], -36), ([1, 1, 1, -1, -1, 1, -1], 36)]

theorem source85_checked : normalize (row ![0, 1, 0, -1, 1, -1] ![0, 1, 0, -1, 1, -1] (-12, 0)) = source85 := by
  decide +kernel

theorem source85_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source85 (momentValues f) = 0 := by
  rw [← source85_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source86 : Sparse := [([0, -1, 1, 0, 1, -1, 0], -36), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, 0, 0, 1, 1, -1, -1], -36), ([0, 0, 1, -1, 1, -1, 0], -36), ([0, 0, 1, -1, 1, 0, -1], -36), ([0, 0, 1, 0, 2, -2, -1], -36), ([0, 0, 1, 0, 2, -1, -2], -36), ([0, 0, 1, 1, 0, -1, -1], -36), ([0, 0, 2, 0, 1, -2, -1], -36), ([0, 0, 2, 0, 1, -1, -2], -36), ([0, 1, 0, 0, 1, -1, -1], -36), ([0, 1, 1, 0, 0, -1, -1], -36), ([1, -1, 1, 1, 1, -1, -1], 36), ([1, 0, 0, 0, 2, -1, -1], 36), ([1, 0, 1, 0, 1, -2, 0], 36), ([1, 0, 1, 0, 1, 0, -2], 36), ([1, 0, 2, 0, 0, -1, -1], 36), ([1, 1, 1, -1, 1, -1, -1], 36)]

theorem source86_checked : normalize (row ![0, 1, 0, 1, -1, -1] ![0, 1, 0, 1, -1, -1] (-12, 0)) = source86 := by
  decide +kernel

theorem source86_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source86 (momentValues f) = 0 := by
  rw [← source86_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source87 : Sparse := [([0, -1, 1, 1, -1, 0, 0], -36), ([0, 0, 1, 0, -1, -1, 1], -36), ([0, 0, 1, 1, -2, 0, 0], -36), ([0, 0, 1, 1, -1, 0, -1], 36), ([0, 0, 1, 1, 0, -1, -1], -36), ([0, 0, 1, 2, -2, -1, 0], -36), ([0, 0, 2, 0, -1, -1, 0], -36), ([0, 0, 2, 1, -2, -1, 0], 36), ([0, 0, 2, 1, -1, -2, 0], -36), ([0, 1, 0, 1, -1, -1, 0], -36), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 1, 1, 1, -1, -1, -1], -36), ([1, -1, 1, 1, -1, -1, 1], 36), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, 0, 0, 1, -1, -1, 1], -36), ([1, 0, 0, 2, -1, -1, 0], 36), ([1, 0, 1, 1, -2, 0, 0], -36), ([1, 0, 1, 1, -1, 0, -1], 36), ([1, 0, 1, 1, 0, -2, 0], 36), ([1, 0, 1, 2, -1, -2, 0], -36), ([1, 0, 2, 0, -1, -1, 0], -36), ([1, 0, 2, 1, -2, -1, 0], 36), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 1, 1, 1, -1, -1, -1], -36)]

theorem source87_checked : normalize (row ![0, 1, 1, -1, -1, 0] ![0, 1, 1, -1, -1, 0] (-12, 0)) = source87 := by
  decide +kernel

theorem source87_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source87 (momentValues f) = 0 := by
  rw [← source87_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
