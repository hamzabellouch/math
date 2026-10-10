import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source416 : Sparse := [([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, 0, -2, 0, -1, 1, 2], 9), ([0, 0, -2, 0, 0, 1, 1], 9), ([0, 0, -2, 1, -1, 1, 1], 9), ([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, -1, 0, -2, 1, 2], 9), ([0, 0, -1, 0, -1, 2, 0], 18), ([0, 0, -1, 1, -2, 1, 1], -9), ([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, 0, 0, -2, 1, 1], 9), ([0, 1, -2, 0, -1, 1, 1], -9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, 0, -2, 1, 1], 9), ([0, 1, -1, 0, -1, 0, 1], 9), ([1, -1, -1, 0, -1, 1, 2], 9), ([1, -1, -1, 0, 0, 1, 1], -9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, 0, -2, 0, 0, 1, 1], 9), ([1, 0, -2, 1, -1, 1, 1], 9), ([1, 0, -1, -1, -1, 1, 2], 9), ([1, 0, -1, -1, 0, 1, 1], 9), ([1, 0, -1, 0, -1, 2, 0], 18), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, 0, -1, -1, 1, 1], -9), ([1, 0, 0, 0, -2, 1, 1], 9), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, 0, -2, 1, 1], 9)]

theorem source416_checked : normalize (row ![0, -1, 0, -1, 1, 1] ![0, 0, 0, 0, -1, 1] (3, 3)) = source416 := by
  decide +kernel

theorem source416_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source416 (momentValues f) = 0 := by
  rw [← source416_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source417 : Sparse := [([0, -1, 1, 0, 1, 0, -1], 9), ([0, -1, 2, 0, 1, -1, -1], -9), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 0, 0, 1, 1, -1, -1], 9), ([0, 0, 1, -1, 1, 0, -1], 9), ([0, 0, 1, -1, 2, -1, -1], -9), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 0, 1, 0, 2, -1, -2], 9), ([0, 0, 1, 1, 1, -1, -2], -9), ([0, 0, 2, 0, 1, -1, -2], 9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 1, 0, 1, -1, -2], -9), ([1, -1, 1, 0, 2, -1, -1], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, 0, 0, 0, 1, 0, -1], -9), ([1, 0, 0, 0, 2, -1, -1], -9), ([1, 0, 0, 1, 1, -1, -1], 9), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 0, 1, 0, 1, -2, 0], -18), ([1, 0, 1, 1, 0, -1, -1], -9), ([1, 0, 1, 1, 1, -1, -2], -9), ([1, 0, 2, -1, 1, -1, -1], -9), ([1, 0, 2, 0, 0, -1, -1], -9), ([1, 1, 0, 0, 1, -1, -1], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, 0, -1, -1], 9), ([1, 1, 1, 0, 1, -1, -2], -9)]

theorem source417_checked : normalize (row ![0, 1, 0, 1, -1, -1] ![0, 0, 0, 0, 1, -1] (0, -3)) = source417 := by
  decide +kernel

theorem source417_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source417 (momentValues f) = 0 := by
  rw [← source417_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source418 : Sparse := [([0, -1, 0, -1, -1, 1, 2], 9), ([0, -1, 0, -1, 0, 1, 1], -9), ([0, 0, -1, -1, -1, 1, 2], -9), ([0, 0, 0, -2, -1, 1, 2], 9), ([0, 0, 0, -1, -2, 1, 2], -9), ([0, 0, 0, -1, 0, 0, 1], 9), ([0, 0, 0, 0, -2, 1, 1], 9), ([0, 0, 0, 0, -1, 0, 1], -9), ([0, 0, 1, -2, -1, 1, 1], -9), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, 0, -1, -1, 0, 1], -9), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, 0, -1, -1, -1, 1, 2], -9), ([1, 0, -1, -1, 0, 1, 1], -9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, 0, -2, 0, 1, 1], -9), ([1, 0, 0, -1, -2, 1, 2], -9), ([1, 0, 0, -1, -1, 2, 0], -18), ([1, 0, 0, 0, -2, 1, 1], 9), ([1, 0, 0, 0, -1, 0, 1], -9), ([1, 0, 1, -1, -2, 1, 1], -9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, 0, -2, -1, 1, 1], -9), ([1, 1, 0, -1, -2, 1, 1], -9), ([1, 1, 0, -1, -1, 0, 1], -9)]

theorem source418_checked : normalize (row ![0, 0, -1, -1, 1, 1] ![0, 0, 0, 0, -1, 1] (0, -3)) = source418 := by
  decide +kernel

theorem source418_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source418 (momentValues f) = 0 := by
  rw [← source418_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source419 : Sparse := [([0, -1, 0, 1, 2, -1, -1], 9), ([0, -1, 0, 2, 1, -1, -1], 9), ([0, 0, -1, 1, 1, 0, -1], 9), ([0, 0, -1, 1, 2, -1, -1], 9), ([0, 0, -1, 2, 1, -1, -1], -9), ([0, 0, 0, 1, 0, 0, -1], 9), ([0, 0, 0, 1, 1, -2, 0], 18), ([0, 0, 0, 2, 0, -1, -1], 9), ([0, 0, 0, 2, 1, -1, -2], 9), ([0, 0, 1, 0, 1, -1, -1], 9), ([0, 0, 1, 1, 0, -1, -1], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 1, 0, 1, 1, -1, -2], 9), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, -1, 0, 1, 2, -1, -1], 9), ([1, -1, 0, 2, 1, -1, -1], 9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, 0, -1, 1, 2, -1, -1], 9), ([1, 0, 0, 0, 1, 0, -1], 9), ([1, 0, 0, 0, 2, -1, -1], -9), ([1, 0, 0, 1, 1, -2, 0], 18), ([1, 0, 0, 1, 2, -1, -2], 9), ([1, 0, 0, 2, 0, -1, -1], 9), ([1, 0, 1, 0, 1, -1, -1], 9), ([1, 0, 1, 1, 0, -1, -1], 9), ([1, 0, 1, 1, 1, -1, -2], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, 0, 1, -1, -1], 9)]

theorem source419_checked : normalize (row ![0, 0, 1, 1, -1, -1] ![0, 0, 0, 0, 1, -1] (3, 3)) = source419 := by
  decide +kernel

theorem source419_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source419 (momentValues f) = 0 := by
  rw [← source419_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source420 : Sparse := [([0, 1, -2, -1, 1, 0, 1], -9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, -1, 0, 0, -1, 1], -9), ([0, 1, -1, 0, 0, 0, 0], 9), ([0, 1, 0, -2, 0, 0, 1], 9), ([0, 1, 0, -1, 0, 0, 0], -9), ([0, 2, -2, -1, 0, 0, 1], 9), ([0, 2, -1, -2, 0, 0, 1], -9), ([0, 2, -1, -1, -1, 0, 1], -9), ([0, 2, -1, -1, 0, -1, 1], 9), ([1, 0, -1, -1, 0, 0, 2], -18), ([1, 1, -2, -1, 0, 1, 1], -9), ([1, 1, -2, 0, 0, 0, 1], -9), ([1, 1, -1, -2, 0, 1, 1], -9), ([1, 1, -1, -2, 1, 0, 1], -9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, 0, -2, 0, 0, 1], 9), ([1, 1, 0, -1, -1, 0, 1], -9), ([1, 1, 0, -1, 0, -1, 1], -9), ([1, 1, 0, -1, 0, 0, 0], -9), ([1, 2, -1, -2, 0, 0, 1], -9), ([1, 2, -1, -1, -1, 0, 1], -9)]

theorem source420_checked : normalize (row ![1, -1, -1, 0, 0, 1] ![1, 0, 0, 0, 0, -1] (0, -3)) = source420 := by
  decide +kernel

theorem source420_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source420 (momentValues f) = 0 := by
  rw [← source420_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source421 : Sparse := [([0, -2, 1, 1, 0, 1, -1], 9), ([0, -2, 2, 1, 0, 0, -1], 9), ([0, -1, 0, 1, 0, 1, -1], 9), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, -1, 1, 0, 0, 0, 0], 9), ([0, -1, 1, 0, 0, 1, -1], -9), ([0, -1, 1, 0, 1, 0, -1], 9), ([0, -1, 1, 1, -1, 0, 0], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 2, -1, 0, -1], 9), ([0, -1, 1, 2, 0, -1, -1], 9), ([0, -1, 2, 0, 0, 0, -1], 9), ([0, -1, 2, 1, -1, 0, -1], -9), ([0, -1, 2, 1, 0, -1, -1], 9), ([0, 0, 1, 1, 0, 0, -2], 18), ([1, -2, 1, 1, 1, 0, -1], 9), ([1, -2, 1, 2, 0, 0, -1], 9), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, -1, 0, 2, 0, 0, -1], -9), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 1, 2, -1, 0, -1], 9), ([1, -1, 1, 2, 0, -1, -1], 9), ([1, -1, 2, 0, 0, 0, -1], 9), ([1, -1, 2, 1, 0, -1, -1], 9), ([1, 0, 1, 1, 0, 0, -2], 18)]

theorem source421_checked : normalize (row ![-1, 1, 1, 0, 0, -1] ![-1, 0, 0, 0, 0, 1] (3, 3)) = source421 := by
  decide +kernel

theorem source421_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source421 (momentValues f) = 0 := by
  rw [← source421_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source422 : Sparse := [([0, 0, -1, 0, -1, 0, 2], 18), ([0, 1, -2, 0, -1, 1, 1], 9), ([0, 1, -2, 1, -1, 0, 1], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 0, 0, 1], 9), ([0, 1, -1, 0, -2, 1, 1], -9), ([0, 1, -1, 0, -1, 1, 0], 9), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, -1, 1, -2, 0, 1], 9), ([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 0, 0, -2, 0, 1], 9), ([0, 1, 0, 0, -1, -1, 1], 9), ([0, 1, 0, 0, -1, 0, 0], 9), ([0, 2, -1, -1, -1, 0, 1], 9), ([0, 2, -1, 0, -2, 0, 1], 9), ([1, 0, -1, 0, -1, 0, 2], 18), ([1, 1, -2, 0, -1, 1, 1], 9), ([1, 1, -2, 0, 0, 0, 1], -9), ([1, 1, -2, 1, -1, 0, 1], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, 0, 0, 1], 9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, -1, 0, 0, 0, 0], 9), ([1, 1, -1, 1, -2, 0, 1], 9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, 0, 0, -2, 0, 1], 9), ([1, 1, 0, 0, -1, -1, 1], 9), ([1, 2, -2, 0, -1, 0, 1], 9), ([1, 2, -1, 0, -1, -1, 1], 9)]

theorem source422_checked : normalize (row ![1, -1, 0, -1, 0, 1] ![1, 0, 0, 0, 0, -1] (3, 3)) = source422 := by
  decide +kernel

theorem source422_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source422 (momentValues f) = 0 := by
  rw [← source422_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source423 : Sparse := [([0, -2, 1, 0, 1, 1, -1], -9), ([0, -2, 1, 0, 2, 0, -1], 9), ([0, -2, 1, 1, 1, 0, -1], 9), ([0, -2, 2, 0, 1, 0, -1], -9), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, -1, 0, 1, 1, 0, -1], -9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, 0, 0, 0], -9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, -1, 1, 0, 2, -1, -1], -9), ([0, -1, 2, 0, 0, 0, -1], 9), ([1, -2, 1, 0, 1, 1, -1], -9), ([1, -2, 2, 0, 1, 0, -1], -9), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, -1, 0, 0, 2, 0, -1], -9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, -1, 2, 0, -1], -9), ([1, -1, 1, 0, 0, 0, 0], -9), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 2, -1, 1, 0, -1], -9), ([1, -1, 2, 0, 0, 0, -1], 9), ([1, -1, 2, 0, 1, -1, -1], -9), ([1, 0, 1, 0, 1, 0, -2], -18)]

theorem source423_checked : normalize (row ![-1, 1, 0, 1, 0, -1] ![-1, 0, 0, 0, 0, 1] (0, -3)) = source423 := by
  decide +kernel

theorem source423_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source423 (momentValues f) = 0 := by
  rw [← source423_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
