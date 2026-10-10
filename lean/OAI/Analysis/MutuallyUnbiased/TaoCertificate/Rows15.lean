import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source120 : Sparse := [([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 1, 1, -2, -1, 0, 1], 9), ([0, 1, 1, -2, -1, 1, 0], 9), ([0, 1, 1, -1, -2, 0, 1], -9), ([0, 1, 1, -1, -2, 1, 0], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, 0, -1, 0], 9), ([0, 1, 1, -1, 0, 0, -1], 9), ([0, 1, 1, 0, -2, 0, 0], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 1, 2, -1, -2, 0, 0], 9), ([0, 1, 2, -1, -1, -1, 0], 9), ([0, 2, 0, -1, -1, 0, 0], 18), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 0, 1, -1, 0, 0, 0], 9), ([1, 1, 1, -2, -1, 0, 1], 9), ([1, 1, 1, -2, -1, 1, 0], 9), ([1, 1, 1, -2, 0, 0, 0], -9), ([1, 1, 1, -1, -2, 1, 0], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 0, -1, 0], 9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, 0, -2, 0, 0], 9), ([1, 1, 1, 0, -1, 0, -1], 9), ([1, 1, 2, -2, -1, 0, 0], 9), ([1, 1, 2, -1, -1, 0, -1], 9), ([1, 2, 0, -1, -1, 0, 0], 18)]

theorem source120_checked : normalize (row ![1, 1, -1, -1, 0, 0] ![-1, 1, 0, 0, 0, 0] (3, 3)) = source120 := by
  decide +kernel

theorem source120_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source120 (momentValues f) = 0 := by
  rw [← source120_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source121 : Sparse := [([0, -1, -2, 1, 1, 0, 1], -9), ([0, -1, -2, 1, 1, 1, 0], 9), ([0, -1, -2, 1, 2, 0, 0], 9), ([0, -1, -2, 2, 1, 0, 0], -9), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 1, 2, 0, -1], -9), ([0, -1, -1, 2, 0, 0, 0], 9), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, -1, 1, 1, 0, -1], 9), ([1, -2, 0, 1, 1, 0, 0], -18), ([1, -1, -2, 1, 1, 0, 1], -9), ([1, -1, -2, 2, 1, 0, 0], -9), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, -1, 0, 2, 0, 0], -9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 1, 2, -1, 0], -9), ([1, -1, -1, 2, 0, 0, 0], 9), ([1, -1, -1, 2, 1, -1, 0], -9), ([1, -1, -1, 2, 1, 0, -1], -9), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, -1, 0], -9)]

theorem source121_checked : normalize (row ![-1, -1, 1, 1, 0, 0] ![1, -1, 0, 0, 0, 0] (0, -3)) = source121 := by
  decide +kernel

theorem source121_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source121 (momentValues f) = 0 := by
  rw [← source121_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source122 : Sparse := [([0, 0, 1, -1, 0, -1, 1], -9), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 1, 1, -2, 1, -1, 0], -9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, 0, 0, -1], -9), ([0, 1, 1, 0, 0, -2, 0], 9), ([0, 1, 2, -2, 0, -1, 0], 9), ([0, 1, 2, -1, -1, -1, 0], -9), ([0, 1, 2, -1, 0, -2, 0], -9), ([0, 1, 2, -1, 0, -1, -1], 9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 1, 1, -2, 0, -1, 1], -9), ([1, 1, 1, -2, 0, 0, 0], -9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, 0, 0], -9), ([1, 1, 1, -1, 0, -2, 1], -9), ([1, 1, 1, -1, 1, -2, 0], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 1, 1, 0, 0, -2, 0], 9), ([1, 1, 1, 0, 0, -1, -1], -9), ([1, 1, 2, -1, -1, -1, 0], -9), ([1, 1, 2, -1, 0, -2, 0], -9), ([1, 2, 0, -1, 0, -1, 0], -18)]

theorem source122_checked : normalize (row ![1, 1, -1, 0, -1, 0] ![-1, 1, 0, 0, 0, 0] (0, -3)) = source122 := by
  decide +kernel

theorem source122_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source122 (momentValues f) = 0 := by
  rw [← source122_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source123 : Sparse := [([0, -2, 0, 1, 0, 1, 0], 18), ([0, -1, -2, 1, 0, 1, 1], 9), ([0, -1, -2, 2, 0, 1, 0], 9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, -1, 2, 0], 9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, -1, 1, 0, 2, -1], 9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, -1, -1, 2, -1, 1, 0], -9), ([0, -1, -1, 2, 0, 0, 0], 9), ([0, -1, -1, 2, 0, 1, -1], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, -1, 1, 0, 0, 0], 9), ([1, -2, 0, 1, 0, 1, 0], 18), ([1, -1, -2, 1, 0, 2, 0], 9), ([1, -1, -2, 1, 1, 1, 0], 9), ([1, -1, -1, 0, 0, 1, 1], 9), ([1, -1, -1, 0, 0, 2, 0], -9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, -1, 2, 0], 9), ([1, -1, -1, 1, 0, 2, -1], 9), ([1, -1, -1, 1, 1, 0, 0], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 2, 0, 0, 0], 9), ([1, -1, -1, 2, 0, 1, -1], 9), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, 0, 1, -1], 9)]

theorem source123_checked : normalize (row ![-1, -1, 1, 0, 1, 0] ![1, -1, 0, 0, 0, 0] (3, 3)) = source123 := by
  decide +kernel

theorem source123_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source123 (momentValues f) = 0 := by
  rw [← source123_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source124 : Sparse := [([0, 0, 1, -1, 0, 0, 0], -9), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 0, 1, -1, 1, 0, -1], 9), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 1, 1, -2, 1, 0, -1], -9), ([0, 1, 1, -1, -1, 0, 0], 9), ([0, 1, 1, -1, 0, 1, -2], -9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 2, -2, 0, 0, -1], 9), ([0, 1, 2, -1, -1, 0, -1], -9), ([0, 1, 2, -1, 0, -1, -1], -9), ([0, 1, 2, -1, 0, 0, -2], 9), ([1, 0, 1, -1, 0, 0, 0], -9), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 1, 1, -2, 0, 0, 0], -9), ([1, 1, 1, -2, 0, 1, -1], -9), ([1, 1, 1, -1, -1, 0, 0], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 0, -1, 0], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, -1, 1, 0, -2], -9), ([1, 1, 1, 0, -1, 0, -1], -9), ([1, 1, 1, 0, 0, -1, -1], 9), ([1, 1, 1, 0, 0, 0, -2], -9), ([1, 1, 2, -1, -1, 0, -1], -9), ([1, 1, 2, -1, 0, -1, -1], -9), ([1, 2, 0, -1, 0, 0, -1], -18)]

theorem source124_checked : normalize (row ![1, 1, -1, 0, 0, -1] ![-1, 1, 0, 0, 0, 0] (0, -3)) = source124 := by
  decide +kernel

theorem source124_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source124 (momentValues f) = 0 := by
  rw [← source124_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source125 : Sparse := [([0, -2, 0, 1, 0, 0, 1], 18), ([0, -1, -2, 1, 0, 0, 2], 9), ([0, -1, -2, 2, 0, 0, 1], 9), ([0, -1, -1, 0, 0, 0, 2], 9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, -1, 1, -1, 0, 2], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 0, -1, 2], -9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 2, -1, 0, 1], -9), ([0, -1, -1, 2, 0, -1, 1], 9), ([0, -1, -1, 2, 0, 0, 0], 9), ([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, -1, 1, 0, -1, 1], 9), ([1, -2, 0, 1, 0, 0, 1], 18), ([1, -1, -2, 1, 0, 1, 1], 9), ([1, -1, -2, 1, 1, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], 9), ([1, -1, -1, 0, 0, 1, 1], -9), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, -1, 1, -1, 0, 2], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 2, 0, -1, 1], 9), ([1, -1, -1, 2, 0, 0, 0], 9), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 1, 0, 0, 0], 9)]

theorem source125_checked : normalize (row ![-1, -1, 1, 0, 0, 1] ![1, -1, 0, 0, 0, 0] (3, 3)) = source125 := by
  decide +kernel

theorem source125_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source125 (momentValues f) = 0 := by
  rw [← source125_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source126 : Sparse := [([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, -1, 0, 0], 9), ([0, 1, 1, 0, -2, -1, 1], -9), ([0, 1, 1, 0, -2, 0, 0], 9), ([0, 1, 1, 0, -1, -2, 1], 9), ([0, 1, 1, 0, 0, -2, 0], 9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 1, 1, -2, -1, 0], 9), ([0, 1, 1, 1, -1, -2, 0], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 2, 0, -2, -1, 0], 9), ([0, 1, 2, 0, -1, -2, 0], 9), ([0, 2, 0, 0, -1, -1, 0], 18), ([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, 0, 0], 9), ([1, 1, 1, -1, 0, -1, 0], -9), ([1, 1, 1, 0, -2, 0, 0], 9), ([1, 1, 1, 0, -1, -2, 1], 9), ([1, 1, 1, 0, -1, 0, -1], -9), ([1, 1, 1, 0, 0, -2, 0], 9), ([1, 1, 1, 0, 0, -1, -1], 9), ([1, 1, 1, 1, -2, -1, 0], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 2, -1, -1, -1, 0], 9), ([1, 1, 2, 0, -1, -1, -1], 9), ([1, 2, 0, 0, -1, -1, 0], 18)]

theorem source126_checked : normalize (row ![1, 1, 0, -1, -1, 0] ![-1, 1, 0, 0, 0, 0] (3, 3)) = source126 := by
  decide +kernel

theorem source126_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source126 (momentValues f) = 0 := by
  rw [← source126_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source127 : Sparse := [([0, -1, -2, 0, 1, 1, 1], -9), ([0, -1, -2, 0, 1, 2, 0], 9), ([0, -1, -2, 0, 2, 1, 0], 9), ([0, -1, -2, 1, 1, 1, 0], -9), ([0, -1, -1, -1, 1, 2, 0], -9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, -1, 0, 2, 1, -1], -9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 1, 1, -1], 9), ([1, -2, 0, 0, 1, 1, 0], -18), ([1, -1, -2, 0, 1, 1, 1], -9), ([1, -1, -2, 1, 1, 1, 0], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 2, 1, 0], -9), ([1, -1, -1, 0, 0, 1, 1], -9), ([1, -1, -1, 0, 0, 2, 0], -9), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, -1, 0, 1, 2, -1], -9), ([1, -1, -1, 0, 2, 0, 0], -9), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, -1, 0, 1, 0, 0], -9)]

theorem source127_checked : normalize (row ![-1, -1, 0, 1, 1, 0] ![1, -1, 0, 0, 0, 0] (0, -3)) = source127 := by
  decide +kernel

theorem source127_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source127 (momentValues f) = 0 := by
  rw [← source127_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
