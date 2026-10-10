import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source128 : Sparse := [([0, 0, 1, 0, -1, 0, 0], -9), ([0, 0, 1, 0, -1, 1, -1], 9), ([0, 0, 1, 0, 0, 0, -1], 9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 1, 1, -1, 0, 0, -1], -9), ([0, 1, 1, 0, -2, 0, 0], 9), ([0, 1, 1, 0, -1, 1, -2], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 2, -1, -1, 0, -1], 9), ([0, 1, 2, 0, -2, 0, -1], -9), ([0, 1, 2, 0, -1, -1, -1], -9), ([0, 1, 2, 0, -1, 0, -2], 9), ([1, 0, 1, 0, -1, 0, 0], -9), ([1, 0, 1, 1, -1, 0, -1], -9), ([1, 1, 1, -1, -1, 0, 0], -9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, 0, -2, 0, 0], 9), ([1, 1, 1, 0, -2, 1, -1], -9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 1, 1, 0, 0, -1, -1], -9), ([1, 1, 1, 0, 0, 0, -2], -9), ([1, 1, 1, 1, -2, 0, -1], -9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, -1, 0, -2], -9), ([1, 1, 2, 0, -2, 0, -1], -9), ([1, 1, 2, 0, -1, -1, -1], -9), ([1, 2, 0, 0, -1, 0, -1], -18)]

theorem source128_checked : normalize (row ![1, 1, 0, -1, 0, -1] ![-1, 1, 0, 0, 0, 0] (0, -3)) = source128 := by
  decide +kernel

theorem source128_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source128 (momentValues f) = 0 := by
  rw [← source128_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source129 : Sparse := [([0, -2, 0, 0, 1, 0, 1], 18), ([0, -1, -2, 0, 1, 0, 2], 9), ([0, -1, -2, 1, 1, 0, 1], 9), ([0, -1, -1, -1, 1, 0, 2], 9), ([0, -1, -1, -1, 2, 0, 1], 9), ([0, -1, -1, 0, 0, 0, 2], 9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, -1, 0, 1, -1, 2], -9), ([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, -1, 0, 2, -1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 0, 1, -1, 1], 9), ([1, -2, 0, 0, 1, 0, 1], 18), ([1, -1, -2, 0, 1, 1, 1], 9), ([1, -1, -2, 0, 2, 0, 1], 9), ([1, -1, -1, -1, 1, 0, 2], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 2, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], 9), ([1, -1, -1, 0, 0, 1, 1], 9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, -1, 0, 2, -1, 1], 9), ([1, -1, -1, 0, 2, 0, 0], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 1, 0, 0], 9), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, -1, 0, 1, 0, 0], 9)]

theorem source129_checked : normalize (row ![-1, -1, 0, 1, 0, 1] ![1, -1, 0, 0, 0, 0] (3, 3)) = source129 := by
  decide +kernel

theorem source129_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source129 (momentValues f) = 0 := by
  rw [← source129_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source130 : Sparse := [([0, 0, 1, 0, 0, -1, 0], 9), ([0, 0, 1, 1, 0, -1, -1], 9), ([0, 1, 1, -1, 0, -1, 0], 9), ([0, 1, 1, -1, 0, 0, -1], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 1, 1, 0, 0, -2, 0], 9), ([0, 1, 1, 0, 1, -2, -1], 9), ([0, 1, 1, 0, 1, -1, -2], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, 0, -2, -1], -9), ([0, 1, 1, 1, 0, -1, -2], 9), ([0, 1, 2, 0, -1, -1, -1], 9), ([0, 1, 2, 0, 0, -2, -1], 9), ([0, 2, 0, 0, 0, -1, -1], 18), ([1, 0, 1, 0, 0, 0, -1], 9), ([1, 0, 1, 0, 1, -1, -1], 9), ([1, 1, 1, -1, 0, -1, 0], 9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, -1, 0, -1], 9), ([1, 1, 1, 0, 0, -2, 0], 9), ([1, 1, 1, 0, 0, 0, -2], -9), ([1, 1, 1, 0, 1, -2, -1], 9), ([1, 1, 1, 0, 1, -1, -2], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, 0, -1, -2], 9), ([1, 1, 2, -1, 0, -1, -1], 9), ([1, 1, 2, 0, 0, -1, -2], 9), ([1, 2, 0, 0, 0, -1, -1], 18)]

theorem source130_checked : normalize (row ![1, 1, 0, 0, -1, -1] ![-1, 1, 0, 0, 0, 0] (3, 3)) = source130 := by
  decide +kernel

theorem source130_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source130 (momentValues f) = 0 := by
  rw [← source130_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source131 : Sparse := [([0, -1, -2, 0, 0, 1, 2], -9), ([0, -1, -2, 0, 0, 2, 1], 9), ([0, -1, -2, 0, 1, 1, 1], 9), ([0, -1, -2, 1, 0, 1, 1], -9), ([0, -1, -1, -1, 0, 2, 1], -9), ([0, -1, -1, 0, 0, 0, 2], 9), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 0, 1, 0], 9), ([1, -2, 0, 0, 0, 1, 1], -18), ([1, -1, -2, 0, 0, 1, 2], -9), ([1, -1, -2, 1, 0, 1, 1], -9), ([1, -1, -1, -1, 0, 1, 2], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, 0, -1, 1, 2], -9), ([1, -1, -1, 0, -1, 2, 1], -9), ([1, -1, -1, 0, 0, 0, 2], 9), ([1, -1, -1, 0, 0, 2, 0], -9), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, -1, 0, 0, 0, 1], -9)]

theorem source131_checked : normalize (row ![-1, -1, 0, 0, 1, 1] ![1, -1, 0, 0, 0, 0] (0, -3)) = source131 := by
  decide +kernel

theorem source131_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source131 (momentValues f) = 0 := by
  rw [← source131_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source132 : Sparse := [([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, 0, 1, -1, 0, 0], -9), ([0, 1, -2, 1, -1, 0, 1], -9), ([0, 1, -2, 2, -1, 0, 0], 9), ([0, 1, -1, 1, -2, 1, 0], -9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, -1, 2, -2, 0, 0], 9), ([0, 1, -1, 2, -1, -1, 0], -9), ([0, 1, -1, 2, -1, 0, -1], -9), ([0, 1, 0, 1, -1, -1, 0], 9), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, 0, 1, -1, 0, 0], -9), ([1, 1, -2, 1, -1, 1, 0], -9), ([1, 1, -2, 1, 0, 0, 0], -9), ([1, 1, -1, 1, -2, 0, 1], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 2, -1, -1, 0], -9), ([1, 1, -1, 2, -1, 0, -1], -9), ([1, 1, 0, 1, -2, 0, 0], -9), ([1, 1, 0, 1, -1, -1, 0], 9), ([1, 1, 0, 1, -1, 0, -1], -9), ([1, 2, -1, 0, -1, 0, 0], -18)]

theorem source132_checked : normalize (row ![1, -1, 1, -1, 0, 0] ![-1, 0, 1, 0, 0, 0] (0, -3)) = source132 := by
  decide +kernel

theorem source132_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source132 (momentValues f) = 0 := by
  rw [← source132_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source133 : Sparse := [([0, -2, 1, 0, 1, 0, 0], 18), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 0, -1, 2, 0, 0], 9), ([0, -1, 1, -2, 2, 0, 0], 9), ([0, -1, 1, -1, 0, 1, 0], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, -1, 2, -1, 0], -9), ([0, -1, 1, -1, 2, 0, -1], 9), ([0, -1, 2, -2, 1, 0, 0], 9), ([0, -1, 2, -1, 0, 0, 0], 9), ([0, -1, 2, -1, 1, -1, 0], 9), ([0, -1, 2, -1, 1, 0, -1], -9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 0, 1, -1, 1, 0, -1], 9), ([1, -2, 1, 0, 1, 0, 0], 18), ([1, -1, 0, -1, 1, 0, 1], 9), ([1, -1, 0, -1, 1, 1, 0], -9), ([1, -1, 0, -1, 2, 0, 0], 9), ([1, -1, 1, -2, 1, 0, 1], 9), ([1, -1, 1, -2, 1, 1, 0], 9), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, -1, 2, 0, -1], 9), ([1, -1, 2, -1, 0, 0, 0], 9), ([1, -1, 2, -1, 1, -1, 0], 9), ([1, 0, 0, -1, 1, 0, 0], 9), ([1, 0, 1, -1, 0, 0, 0], 9)]

theorem source133_checked : normalize (row ![-1, 1, -1, 1, 0, 0] ![1, 0, -1, 0, 0, 0] (3, 3)) = source133 := by
  decide +kernel

theorem source133_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source133 (momentValues f) = 0 := by
  rw [← source133_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source134 : Sparse := [([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, -1, 1, 0, 0, 0], 9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 1, -2, 1, 0, -1, 1], -9), ([0, 1, -2, 2, 0, -1, 0], 9), ([0, 1, -1, 1, -1, 0, 0], -9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, -1, 2, -1, -1, 0], 9), ([0, 1, -1, 2, 0, -2, 0], -9), ([0, 1, -1, 2, 0, -1, -1], -9), ([0, 1, 0, 1, 0, -2, 0], 9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 1, -2, 1, 0, 0, 0], -9), ([1, 1, -2, 1, 1, -1, 0], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, 0, -2, 1], -9), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, -1, 1, 1, -2, 0], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 2, 0, -2, 0], -9), ([1, 1, -1, 2, 0, -1, -1], -9), ([1, 1, 0, 1, -1, -1, 0], -9), ([1, 1, 0, 1, 0, -2, 0], 9), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 2, -1, 0, 0, -1, 0], -18)]

theorem source134_checked : normalize (row ![1, -1, 1, 0, -1, 0] ![-1, 0, 1, 0, 0, 0] (0, -3)) = source134 := by
  decide +kernel

theorem source134_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source134 (momentValues f) = 0 := by
  rw [← source134_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source135 : Sparse := [([0, -2, 1, 0, 0, 1, 0], 18), ([0, -1, 0, -1, 0, 1, 1], 9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 1, -2, 1, 1, 0], 9), ([0, -1, 1, -1, -1, 2, 0], 9), ([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 1, -1, 0, 2, -1], 9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 2, -2, 0, 1, 0], 9), ([0, -1, 2, -1, -1, 1, 0], 9), ([0, -1, 2, -1, 0, 0, 0], 9), ([0, -1, 2, -1, 0, 1, -1], -9), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, -1, 0, 1, -1], 9), ([1, -2, 1, 0, 0, 1, 0], 18), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 0, -1, 0, 2, 0], -9), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, -1, 1, -2, 0, 1, 1], 9), ([1, -1, 1, -2, 0, 2, 0], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, -1, 2, 0], 9), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, -1, 0, 2, -1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 2, -1, -1, 1, 0], 9), ([1, -1, 2, -1, 0, 0, 0], 9), ([1, 0, 0, -1, 0, 1, 0], 9), ([1, 0, 1, -1, -1, 1, 0], 9)]

theorem source135_checked : normalize (row ![-1, 1, -1, 0, 1, 0] ![1, 0, -1, 0, 0, 0] (3, 3)) = source135 := by
  decide +kernel

theorem source135_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source135 (momentValues f) = 0 := by
  rw [← source135_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
