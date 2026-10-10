import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source344 : Sparse := [([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, 0, 0, 1, 1, -1], 9), ([0, 0, -2, 1, 1, 1, -1], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, -1, -1, 1, 2, -1], 9), ([0, 0, -1, 0, 1, 2, -2], 9), ([0, 0, -1, 0, 2, 0, -1], 18), ([0, 0, -1, 1, 1, 1, -2], 9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 0, 0, 0, 0, 1, -1], 9), ([0, 0, 0, 0, 1, 1, -2], 9), ([0, 1, -2, 0, 1, 1, -1], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, -1, 0, 1, 1, -2], -9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, -1, 0, 1, 2, -1], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, 0, -2, 0, 1, 1, 0], -9), ([1, 0, -2, 0, 1, 2, -1], 9), ([1, 0, -2, 1, 1, 1, -1], 9), ([1, 0, -1, -1, 1, 1, 0], 9), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 0, 2, 0, -1], 18), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 0, -1, 1, 1, 1, -2], 9), ([1, 0, 0, 0, 1, 1, -2], 9), ([1, 1, -2, 0, 1, 1, -1], 9), ([1, 1, -1, -1, 1, 1, -1], 9)]

theorem source344_checked : normalize (row ![0, -1, 0, 1, 1, -1] ![0, 0, 0, -1, 1, 0] (3, 3)) = source344 := by
  decide +kernel

theorem source344_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source344 (momentValues f) = 0 := by
  rw [← source344_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source345 : Sparse := [([0, -1, 1, 0, -1, -1, 2], -9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, 0, 0, 0, 0, -1, 1], 9), ([0, 0, 0, 1, -1, -1, 1], -9), ([0, 0, 1, -1, 0, -1, 1], -9), ([0, 0, 1, 0, -1, -2, 2], 9), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 1, 1, -1, -2, 1], 9), ([0, 0, 2, 0, -1, -2, 1], -9), ([0, 0, 2, 0, -1, -1, 0], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, 0, -1, -2, 1], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 2, 0, -1, -1, 1], -9), ([1, 0, 0, 0, -1, -1, 2], -9), ([1, 0, 1, -1, -1, -1, 2], -9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 0, 1, 0, -2, 0, 1], -18), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 1, 1, -1, -1, 0], -9), ([1, 0, 2, -1, -1, -1, 1], -9), ([1, 0, 2, 0, -1, -2, 1], -9), ([1, 0, 2, 0, -1, -1, 0], 9), ([1, 1, 0, 0, -1, -1, 1], -9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, 0, -1, -2, 1], -9), ([1, 1, 1, 0, -1, -1, 0], -9)]

theorem source345_checked : normalize (row ![0, 1, 0, -1, -1, 1] ![0, 0, 0, 1, -1, 0] (0, -3)) = source345 := by
  decide +kernel

theorem source345_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source345 (momentValues f) = 0 := by
  rw [← source345_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source346 : Sparse := [([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, 0, -1, 0, 1, 1, -1], 9), ([0, 0, 0, -2, 1, 1, 0], 9), ([0, 0, 0, -2, 1, 2, -1], 9), ([0, 0, 0, -1, 1, 2, -2], 9), ([0, 0, 0, -1, 2, 0, -1], 18), ([0, 0, 0, 0, 1, 1, -2], 9), ([0, 0, 1, -2, 1, 1, -1], -9), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 0, 1, -1, 1, 1, -2], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, 0, -2, 1, 1, -1], 9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 1, 0, -1, 1, 1, -2], -9), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, -1, 0, -1, 1, 2, -1], 9), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, 0, -1, -1, 1, 1, 0], -9), ([1, 0, -1, -1, 1, 2, -1], 9), ([1, 0, -1, 0, 1, 1, -1], 9), ([1, 0, 0, -2, 1, 1, 0], 9), ([1, 0, 0, -1, 0, 1, 0], 9), ([1, 0, 0, -1, 2, 0, -1], 18), ([1, 0, 0, 0, 0, 1, -1], 9), ([1, 0, 0, 0, 1, 1, -2], 9), ([1, 0, 1, -1, 1, 1, -2], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, 0, -2, 1, 1, -1], 9)]

theorem source346_checked : normalize (row ![0, 0, -1, 1, 1, -1] ![0, 0, 0, -1, 1, 0] (3, 3)) = source346 := by
  decide +kernel

theorem source346_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source346 (momentValues f) = 0 := by
  rw [← source346_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source347 : Sparse := [([0, -1, 0, 1, -1, -1, 2], -9), ([0, -1, 0, 1, 0, -1, 1], 9), ([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, -1, 2, -1, -1, 1], -9), ([0, 0, 0, 0, 0, -1, 1], -9), ([0, 0, 0, 1, -1, -2, 2], 9), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 0, 0, 2, -1, -2, 1], 9), ([0, 0, 1, 1, -1, -2, 1], -9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 1, 0, 0, -1, -1, 1], 9), ([0, 1, 0, 1, -1, -2, 1], -9), ([1, -1, 0, 2, -1, -1, 1], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, 0, -1, 1, -1, -1, 2], -9), ([1, 0, 0, 0, -1, -1, 2], -9), ([1, 0, 0, 0, 0, -1, 1], -9), ([1, 0, 0, 1, -2, 0, 1], -18), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 0, 0, 2, -1, -1, 0], -9), ([1, 0, 1, 0, -1, -1, 1], -9), ([1, 0, 1, 1, -1, -2, 1], -9), ([1, 0, 1, 1, -1, -1, 0], 9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, 0, 0, -1, -1, 1], 9), ([1, 1, 0, 1, -1, -2, 1], -9), ([1, 1, 0, 1, -1, -1, 0], -9)]

theorem source347_checked : normalize (row ![0, 0, 1, -1, -1, 1] ![0, 0, 0, 1, -1, 0] (0, -3)) = source347 := by
  decide +kernel

theorem source347_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source347 (momentValues f) = 0 := by
  rw [← source347_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source348 : Sparse := [([0, -2, -1, 0, 1, 0, 2], -9), ([0, -2, 0, 0, 1, 0, 1], 9), ([0, -1, -2, 0, 1, 0, 2], 9), ([0, -1, -2, 0, 1, 1, 1], -9), ([0, -1, -1, -1, 1, 0, 2], 9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, -1, 0, 1, -1, 2], -9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, 0, 0, 0, 0, 1], -9), ([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, -1, 0, 0, 0, 1], 9), ([1, -2, -1, 0, 1, 0, 2], -9), ([1, -2, -1, 0, 1, 1, 1], -9), ([1, -2, -1, 1, 1, 0, 1], -9), ([1, -2, 0, 0, 1, 0, 1], 9), ([1, -1, -2, 1, 1, 0, 1], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, 0, 1, -1, 2], -9), ([1, -1, -1, 0, 2, 0, 0], -18), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 0, 0, 0, 0, 1], -9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, 0, -2, 0, 1, 0, 1], -9), ([1, 0, -1, 0, 1, -1, 1], -9)]

theorem source348_checked : normalize (row ![-1, -1, 0, 1, 0, 1] ![0, 0, 0, -1, 0, 1] (0, -3)) = source348 := by
  decide +kernel

theorem source348_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source348 (momentValues f) = 0 := by
  rw [← source348_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source349 : Sparse := [([0, 0, 1, 0, -1, 1, -1], 9), ([0, 0, 1, 0, 0, 0, -1], 9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 0, 2, 0, -1, 0, -1], 9), ([0, 1, 0, 0, -1, 1, -1], 9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 1, 1, 0, -2, 0, 0], 18), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, -1, 0, -2], 9), ([0, 1, 2, -1, -1, 0, -1], 9), ([0, 1, 2, 0, -1, -1, -1], -9), ([0, 1, 2, 0, -1, 0, -2], 9), ([0, 2, 1, -1, -1, 0, -1], 9), ([0, 2, 1, 0, -1, -1, -1], 9), ([1, 0, 1, 0, -1, 1, -1], 9), ([1, 0, 2, 0, -1, 0, -1], 9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 1, 0, 0, 0, 0, -1], 9), ([1, 1, 0, 1, -1, 0, -1], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, 0, -2, 0, 0], 18), ([1, 1, 1, 0, -1, 1, -2], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 2, -1, -1, 0, -1], 9), ([1, 2, 0, 0, -1, 0, -1], -9), ([1, 2, 1, -1, -1, 0, -1], 9), ([1, 2, 1, 0, -1, -1, -1], 9), ([1, 2, 1, 0, -1, 0, -2], 9)]

theorem source349_checked : normalize (row ![1, 1, 0, -1, 0, -1] ![0, 0, 0, 1, 0, -1] (3, 3)) = source349 := by
  decide +kernel

theorem source349_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source349 (momentValues f) = 0 := by
  rw [← source349_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source350 : Sparse := [([0, -2, 0, -1, 1, 0, 2], 9), ([0, -2, 0, -1, 1, 1, 1], 9), ([0, -2, 0, 0, 1, 0, 1], 9), ([0, -2, 1, -1, 1, 0, 1], -9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, 0, -2, 1, 1, 1], 9), ([0, -1, 0, -1, 1, -1, 2], 9), ([0, -1, 0, -1, 2, 0, 0], 18), ([0, -1, 0, 0, 0, 0, 1], 9), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 1, -2, 1, 0, 1], 9), ([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, 0, -1, -1, 1, 0, 1], 9), ([0, 0, 0, -1, 1, -1, 1], 9), ([1, -2, 0, -1, 1, 1, 1], 9), ([1, -2, 0, 0, 1, 0, 1], 9), ([1, -1, -1, -1, 1, 0, 2], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, 0, -2, 1, 0, 2], 9), ([1, -1, 0, -2, 1, 1, 1], 9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 0, -1, 2, 0, 0], 18), ([1, -1, 1, -2, 1, 0, 1], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, 0, -2, 1, 0, 1], -9), ([1, 0, 0, -1, 0, 0, 1], 9), ([1, 0, 0, -1, 1, -1, 1], 9)]

theorem source350_checked : normalize (row ![-1, 0, -1, 1, 0, 1] ![0, 0, 0, -1, 0, 1] (3, 3)) = source350 := by
  decide +kernel

theorem source350_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source350 (momentValues f) = 0 := by
  rw [← source350_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source351 : Sparse := [([0, 0, 0, 1, 0, 0, -1], -9), ([0, 0, 0, 2, -1, 0, -1], 9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, 0, 0, -1, 1, -1], -9), ([0, 1, 0, 0, 0, 0, -1], 9), ([0, 1, 0, 1, -1, 1, -2], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 1, 0, 2, -1, 0, -2], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, -1, 0, -2], -9), ([0, 2, -1, 1, -1, 0, -1], -9), ([0, 2, 0, 1, -1, 0, -2], 9), ([1, 0, 0, 1, -1, 1, -1], -9), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 2, -1, 0, -1], 9), ([1, 0, 1, 1, -1, 0, -1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 2, -1, 0, -1], -9), ([1, 1, 0, 1, -2, 0, 0], -18), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 1, 0, 2, -1, -1, -1], -9), ([1, 1, 0, 2, -1, 0, -2], -9), ([1, 1, 1, 0, -1, 0, -1], -9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, -1, 0, -2], -9), ([1, 2, 0, 0, -1, 0, -1], -9), ([1, 2, 0, 1, -1, -1, -1], -9)]

theorem source351_checked : normalize (row ![1, 0, 1, -1, 0, -1] ![0, 0, 0, 1, 0, -1] (0, -3)) = source351 := by
  decide +kernel

theorem source351_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source351 (momentValues f) = 0 := by
  rw [← source351_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
