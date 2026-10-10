import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source280 : Sparse := [([0, -2, 0, 1, 0, 1, 0], 9), ([0, -2, 0, 1, 0, 2, -1], -9), ([0, -1, -1, 1, 0, 2, -1], 9), ([0, -1, 0, 0, 0, 1, 0], -9), ([0, -1, 0, 0, 1, 1, -1], 9), ([0, -1, 0, 1, -1, 2, -1], -9), ([0, -1, 0, 1, 0, 2, -2], 9), ([0, -1, 0, 1, 1, 1, -2], -9), ([0, -1, 1, 0, 0, 1, -1], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, 0, 0, 0, 1, -1], 9), ([1, -2, 0, 1, 0, 1, 0], 9), ([1, -2, 0, 1, 0, 2, -1], -9), ([1, -2, 0, 1, 1, 1, -1], -9), ([1, -2, 1, 1, 0, 1, -1], -9), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, 0, 0, 0, 1, 0], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 0, 1, -1, 2, -1], -9), ([1, -1, 0, 2, 0, 0, -1], -18), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, 1, -2], -9), ([1, 0, 0, 1, -1, 1, -1], -9), ([1, 0, 0, 1, 0, 1, -2], -9)]

theorem source280_checked : normalize (row ![-1, 0, 1, 0, 1, -1] ![0, 0, -1, 0, 1, 0] (0, -3)) = source280 := by
  decide +kernel

theorem source280_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source280 (momentValues f) = 0 := by
  rw [← source280_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source281 : Sparse := [([0, 0, 0, -1, 0, -1, 2], 9), ([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 0, 0, 0, -1, 1], 9), ([0, 0, 1, -1, 0, -1, 1], -9), ([0, 1, -1, -1, 0, -1, 2], 9), ([0, 1, 0, -2, 0, 0, 1], 18), ([0, 1, 0, -1, -1, -1, 2], -9), ([0, 1, 0, -1, 0, -2, 2], 9), ([0, 1, 0, -1, 1, -1, 0], 9), ([0, 1, 0, 0, -1, -1, 1], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, 0, -2, 1], 9), ([0, 1, 1, -1, 0, -1, 0], 9), ([0, 2, -1, -1, 0, -1, 1], 9), ([0, 2, 0, -1, -1, -1, 1], 9), ([1, 0, 0, -1, 0, -1, 2], 9), ([1, 0, 0, -1, 1, -1, 1], 9), ([1, 1, -1, -1, 0, -1, 2], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, 0, -2, 0, 0, 1], 18), ([1, 1, 0, -1, 1, -2, 1], 9), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 1, 0, 0, 0, -1, 0], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, 0, -1, 0], 9), ([1, 2, -1, -1, 0, -1, 1], 9), ([1, 2, 0, -1, -1, -1, 1], 9), ([1, 2, 0, -1, 0, -2, 1], 9), ([1, 2, 0, -1, 0, -1, 0], -9)]

theorem source281_checked : normalize (row ![1, 0, -1, 0, -1, 1] ![0, 0, 1, 0, -1, 0] (3, 3)) = source281 := by
  decide +kernel

theorem source281_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source281 (momentValues f) = 0 := by
  rw [← source281_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source282 : Sparse := [([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, -1, 2, 0], -9), ([0, 0, -2, 1, -1, 2, 0], 9), ([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, -1, 0, 0, 1, 0], 9), ([0, 0, -1, 1, -2, 2, 0], -9), ([0, 0, -1, 1, -1, 2, -1], 9), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, 0, 0, -1, 1, 0], -9), ([0, 0, 0, 1, -2, 1, 0], 9), ([0, 1, -2, 1, -1, 1, 0], -9), ([0, 1, -1, 0, -1, 1, 0], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, -1, 2, 0], -9), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, 0, -2, 1, -1, 1, 1], -9), ([1, 0, -2, 1, 0, 1, 0], -9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, -1, 1, -2, 1, 1], -9), ([1, 0, -1, 1, -2, 2, 0], -9), ([1, 0, -1, 2, -1, 0, 0], -18), ([1, 0, 0, 0, -1, 1, 0], -9), ([1, 0, 0, 1, -2, 1, 0], 9), ([1, 0, 0, 1, -1, 1, -1], -9), ([1, 1, -1, 1, -2, 1, 0], -9), ([1, 1, -1, 1, -1, 1, -1], -9)]

theorem source282_checked : normalize (row ![0, -1, 1, -1, 1, 0] ![0, 0, -1, 0, 1, 0] (0, -3)) = source282 := by
  decide +kernel

theorem source282_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source282 (momentValues f) = 0 := by
  rw [← source282_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source283 : Sparse := [([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 2, -1, 0], 9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, -1, 2, -1, 1, -1, 0], -9), ([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 1, -2, 1, 0, 0], 18), ([0, 0, 1, -1, 0, -1, 1], -9), ([0, 0, 1, -1, 1, -2, 1], 9), ([0, 0, 1, -1, 2, -1, -1], 9), ([0, 0, 1, 0, 0, -1, 0], 9), ([0, 0, 2, -1, 0, -1, 0], 9), ([0, 0, 2, -1, 1, -2, 0], 9), ([0, 0, 2, -1, 1, -1, -1], 9), ([0, 1, 0, -1, 1, -1, 0], 9), ([0, 1, 1, -1, 0, -1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, -1, 2, -1, 0], 9), ([1, 0, 0, -1, 1, -1, 1], 9), ([1, 0, 0, -1, 2, -1, 0], -9), ([1, 0, 0, 0, 1, -1, 0], 9), ([1, 0, 1, -2, 1, 0, 0], 18), ([1, 0, 1, -1, 2, -2, 0], 9), ([1, 0, 1, -1, 2, -1, -1], 9), ([1, 0, 1, 0, 1, -1, -1], 9), ([1, 0, 2, -1, 0, -1, 0], 9), ([1, 0, 2, -1, 1, -1, -1], 9), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 1, 1, -1, 0, -1, 0], 9), ([1, 1, 1, -1, 1, -2, 0], 9), ([1, 1, 1, -1, 1, -1, -1], -9)]

theorem source283_checked : normalize (row ![0, 1, -1, 1, -1, 0] ![0, 0, 1, 0, -1, 0] (3, 3)) = source283 := by
  decide +kernel

theorem source283_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source283 (momentValues f) = 0 := by
  rw [← source283_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source284 : Sparse := [([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, -1, 1, 0, 2, -1], -9), ([0, 0, -2, 1, 0, 2, -1], 9), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 0, 1, 1, -1], 9), ([0, 0, -1, 1, -1, 2, -1], -9), ([0, 0, -1, 1, 0, 2, -2], 9), ([0, 0, -1, 1, 1, 1, -2], -9), ([0, 0, 0, 0, 0, 1, -1], -9), ([0, 0, 0, 1, -1, 1, -1], 9), ([0, 1, -2, 1, 0, 1, -1], -9), ([0, 1, -1, 0, 0, 1, -1], 9), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, -1, 1, 0, 2, -1], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, 0, -2, 1, 0, 1, 0], -9), ([1, 0, -2, 1, 1, 1, -1], -9), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 0, -1, 1, -1, 2, -1], -9), ([1, 0, -1, 2, 0, 0, -1], -18), ([1, 0, 0, 0, 0, 1, -1], -9), ([1, 0, 0, 1, -1, 1, -1], 9), ([1, 0, 0, 1, 0, 1, -2], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, 1, -2], -9)]

theorem source284_checked : normalize (row ![0, -1, 1, 0, 1, -1] ![0, 0, -1, 0, 1, 0] (0, -3)) = source284 := by
  decide +kernel

theorem source284_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source284 (momentValues f) = 0 := by
  rw [← source284_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source285 : Sparse := [([0, -1, 1, -1, 0, -1, 2], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, -1, 2, -1, 0, -1, 1], -9), ([0, 0, 0, -1, 0, -1, 2], 9), ([0, 0, 1, -2, 0, 0, 1], 18), ([0, 0, 1, -1, -1, -1, 2], -9), ([0, 0, 1, -1, 0, -2, 2], 9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 2, -1, -1, -1, 1], 9), ([0, 0, 2, -1, 0, -2, 1], 9), ([0, 0, 2, -1, 0, -1, 0], 9), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([1, -1, 1, -1, 0, -1, 2], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, 0, 0, -1, 0, -1, 2], 9), ([1, 0, 0, -1, 1, -1, 1], -9), ([1, 0, 0, 0, 0, -1, 1], 9), ([1, 0, 1, -2, 0, 0, 1], 18), ([1, 0, 1, -1, 1, -2, 1], 9), ([1, 0, 1, -1, 1, -1, 0], 9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 2, -1, -1, -1, 1], 9), ([1, 0, 2, -1, 0, -1, 0], 9), ([1, 1, 0, -1, 0, -1, 1], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, 0, -2, 1], 9), ([1, 1, 1, -1, 0, -1, 0], -9)]

theorem source285_checked : normalize (row ![0, 1, -1, 0, -1, 1] ![0, 0, 1, 0, -1, 0] (3, 3)) = source285 := by
  decide +kernel

theorem source285_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source285 (momentValues f) = 0 := by
  rw [← source285_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source286 : Sparse := [([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 0, 1, -1, 2, -1], 9), ([0, -1, 0, 1, 0, 1, -1], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, -1, 1, 0, 1, -1], 9), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 0, 0, 1, -2, 1, 0], 9), ([0, 0, 0, 1, -2, 2, -1], 9), ([0, 0, 0, 2, -1, 0, -1], 18), ([0, 0, 1, 0, -1, 1, -1], 9), ([0, 0, 1, 1, -2, 1, -1], -9), ([0, 0, 1, 1, -1, 1, -2], 9), ([0, 1, 0, 1, -2, 1, -1], 9), ([0, 1, 0, 1, -1, 1, -2], 9), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 0, -1, 1, -1, 2, -1], 9), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 0, 0, 0, 0, 1, -1], 9), ([1, 0, 0, 1, -2, 1, 0], 9), ([1, 0, 0, 1, -1, 2, -2], 9), ([1, 0, 0, 1, 0, 1, -2], -9), ([1, 0, 0, 2, -1, 0, -1], 18), ([1, 0, 1, 1, -1, 1, -2], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 1, 0, 1, -2, 1, -1], 9), ([1, 1, 0, 1, -1, 1, -2], 9)]

theorem source286_checked : normalize (row ![0, 0, 1, -1, 1, -1] ![0, 0, -1, 0, 1, 0] (3, 3)) = source286 := by
  decide +kernel

theorem source286_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source286 (momentValues f) = 0 := by
  rw [← source286_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source287 : Sparse := [([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, 0, -1, -1, 2, -1, 1], -9), ([0, 0, -1, 0, 1, -1, 1], 9), ([0, 0, 0, -1, 0, -1, 2], 9), ([0, 0, 0, -1, 1, -2, 2], -9), ([0, 0, 0, -1, 2, -2, 1], 9), ([0, 0, 0, 0, 0, -1, 1], -9), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 0, 1, -1, 1, -2, 1], -9), ([0, 1, 0, -1, 1, -2, 1], 9), ([0, 1, 0, -1, 1, -1, 0], -9), ([1, -1, 0, -1, 1, -1, 2], -9), ([1, -1, 0, -1, 2, -1, 1], -9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, 0, -1, -1, 1, -1, 2], -9), ([1, 0, 0, -2, 1, 0, 1], -18), ([1, 0, 0, -1, 0, -1, 2], 9), ([1, 0, 0, -1, 1, -2, 2], -9), ([1, 0, 0, -1, 2, -1, 0], -9), ([1, 0, 0, 0, 0, -1, 1], -9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 0, 1, -1, 1, -2, 1], -9), ([1, 0, 1, -1, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, 0, -1, 0, -1, 1], -9)]

theorem source287_checked : normalize (row ![0, 0, -1, 1, -1, 1] ![0, 0, 1, 0, -1, 0] (0, -3)) = source287 := by
  decide +kernel

theorem source287_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source287 (momentValues f) = 0 := by
  rw [← source287_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
