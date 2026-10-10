import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source384 : Sparse := [([0, -2, -1, 2, 0, 1, 0], -9), ([0, -2, 0, 1, 0, 1, 0], 9), ([0, -1, -2, 1, 1, 1, 0], -9), ([0, -1, -2, 2, 0, 1, 0], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, -1, -1, 2, -1, 1, 0], -9), ([0, -1, -1, 2, 0, 1, -1], 9), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, 0, -1, 1, 0, 0, 0], 9), ([0, 0, -1, 1, 0, 1, -1], -9), ([1, -2, -1, 1, 0, 1, 1], -9), ([1, -2, -1, 1, 1, 1, 0], -9), ([1, -2, -1, 2, 0, 1, 0], -9), ([1, -2, 0, 1, 0, 1, 0], 9), ([1, -1, -2, 1, 0, 1, 1], -9), ([1, -1, -1, 0, 0, 2, 0], -18), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 2, -1, 1, 0], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, 0, -2, 1, 0, 1, 0], -9), ([1, 0, -1, 1, -1, 1, 0], -9)]

theorem source384_checked : normalize (row ![-1, -1, 1, 0, 1, 0] ![0, 0, 1, 0, -1, 0] (0, -3)) = source384 := by
  decide +kernel

theorem source384_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source384 (momentValues f) = 0 := by
  rw [← source384_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source385 : Sparse := [([0, 0, 1, -1, 0, -1, 1], -9), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 0, 2, -1, 0, -1, 0], 9), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 1, 0, -1, 1, -1, 0], 9), ([0, 1, 1, -2, 0, -1, 1], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, -1, 0, 0], 9), ([0, 1, 1, 0, 0, -2, 0], 18), ([0, 1, 2, -2, 0, -1, 0], 9), ([0, 1, 2, -1, -1, -1, 0], -9), ([0, 1, 2, -1, 0, -1, -1], 9), ([0, 2, 1, -1, -1, -1, 0], 9), ([0, 2, 1, -1, 0, -1, -1], 9), ([1, 0, 1, -1, 1, -1, 0], 9), ([1, 0, 2, -1, 0, -1, 0], 9), ([1, 1, 0, -1, 0, -1, 1], 9), ([1, 1, 0, -1, 0, 0, 0], 9), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 1, 1, -2, 1, -1, 0], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, 0, -2, 0], 18), ([1, 1, 2, -1, 0, -1, -1], 9), ([1, 2, 0, -1, 0, -1, 0], -9), ([1, 2, 1, -2, 0, -1, 0], 9), ([1, 2, 1, -1, -1, -1, 0], 9), ([1, 2, 1, -1, 0, -1, -1], 9)]

theorem source385_checked : normalize (row ![1, 1, -1, 0, -1, 0] ![0, 0, -1, 0, 1, 0] (3, 3)) = source385 := by
  decide +kernel

theorem source385_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source385 (momentValues f) = 0 := by
  rw [← source385_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source386 : Sparse := [([0, -2, 0, 1, -1, 1, 1], 9), ([0, -2, 0, 1, 0, 1, 0], 9), ([0, -2, 0, 2, -1, 1, 0], 9), ([0, -2, 1, 1, -1, 1, 0], -9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, 0, 0, -1, 2, 0], 18), ([0, -1, 0, 1, -2, 1, 1], -9), ([0, -1, 0, 1, -1, 0, 1], 9), ([0, -1, 0, 1, 0, 1, -1], 9), ([0, -1, 0, 2, -2, 1, 0], 9), ([0, -1, 1, 1, -2, 1, 0], 9), ([0, -1, 1, 1, -1, 0, 0], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, 0, 1, -2, 1, 0], 9), ([1, -2, 0, 1, -1, 1, 1], 9), ([1, -2, 0, 1, 0, 1, 0], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, -1, 2, -1, 1, 0], 9), ([1, -1, 0, 0, -1, 2, 0], 18), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, -1, 0, 2, -1, 1, -1], 9), ([1, -1, 1, 1, -2, 1, 0], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 0, 0, 1, -2, 1, 0], 9), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 0, 0, 1, -1, 1, -1], -9)]

theorem source386_checked : normalize (row ![-1, 0, 1, -1, 1, 0] ![0, 0, 1, 0, -1, 0] (3, 3)) = source386 := by
  decide +kernel

theorem source386_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source386 (momentValues f) = 0 := by
  rw [← source386_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source387 : Sparse := [([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, 0, -2, 1, -1, 1], -9), ([0, 1, 0, -2, 2, -1, 0], 9), ([0, 1, 0, -1, 0, 0, 0], -9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 1, 0, -1, 2, -1, -1], -9), ([0, 1, 1, -2, 1, -1, 0], -9), ([0, 1, 1, -1, 0, -1, 0], 9), ([0, 2, -1, -1, 1, -1, 0], -9), ([0, 2, 0, -2, 1, -1, 0], 9), ([1, 0, 0, -1, 1, -1, 1], 9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 0, 0, -1, 2, -1, 0], -9), ([1, 0, 1, -1, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 2, -1, 0], -9), ([1, 1, 0, -2, 1, -1, 1], -9), ([1, 1, 0, -1, 0, -1, 1], -9), ([1, 1, 0, -1, 0, 0, 0], -9), ([1, 1, 0, 0, 1, -2, 0], -18), ([1, 1, 1, -2, 1, -1, 0], -9), ([1, 1, 1, -1, 0, -1, 0], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 2, 0, -1, 0, -1, 0], -9), ([1, 2, 0, -1, 1, -1, -1], -9)]

theorem source387_checked : normalize (row ![1, 0, -1, 1, -1, 0] ![0, 0, -1, 0, 1, 0] (0, -3)) = source387 := by
  decide +kernel

theorem source387_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source387 (momentValues f) = 0 := by
  rw [← source387_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source388 : Sparse := [([0, -2, 0, 1, 0, 1, 0], 9), ([0, -2, 0, 1, 1, 1, -1], 9), ([0, -2, 0, 2, 0, 1, -1], 9), ([0, -2, 1, 1, 0, 1, -1], -9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, 0, 0, 0, 2, -1], 18), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 1, 1, 1, -2], 9), ([0, -1, 0, 2, -1, 1, -1], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 1, 0, 0, -1], 9), ([0, -1, 1, 1, 0, 1, -2], 9), ([0, 0, -1, 1, 0, 1, -1], 9), ([0, 0, 0, 1, -1, 1, -1], 9), ([1, -2, 0, 1, 0, 1, 0], 9), ([1, -2, 0, 1, 1, 1, -1], 9), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 2, 0, 1, -1], 9), ([1, -1, 0, 0, 0, 2, -1], 18), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, -1, 0, 1, 1, 1, -2], 9), ([1, -1, 0, 2, 0, 1, -2], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, 1, -2], 9), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 0, 0, 1, -1, 1, -1], 9), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 0, 0, 1, 0, 1, -2], -9)]

theorem source388_checked : normalize (row ![-1, 0, 1, 0, 1, -1] ![0, 0, 1, 0, -1, 0] (3, 3)) = source388 := by
  decide +kernel

theorem source388_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source388 (momentValues f) = 0 := by
  rw [← source388_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source389 : Sparse := [([0, 0, 0, -1, 0, -1, 2], 9), ([0, 0, 0, -1, 0, 0, 1], -9), ([0, 1, -1, -1, 0, 0, 1], 9), ([0, 1, 0, -2, 0, -1, 2], -9), ([0, 1, 0, -2, 1, -1, 1], 9), ([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 0, -1, 0, 0, 0], 9), ([0, 1, 0, -1, 1, -1, 0], -9), ([0, 1, 1, -2, 0, -1, 1], -9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 2, -1, -1, 0, -1, 1], -9), ([0, 2, 0, -2, 0, -1, 1], 9), ([1, 0, 0, -1, 0, -1, 2], 9), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 0, -1, 1, -1, 1], -9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 1, -1, -1, 0, -1, 2], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, 0, -2, 0, -1, 2], -9), ([1, 1, 0, -1, -1, -1, 2], -9), ([1, 1, 0, -1, -1, 0, 1], -9), ([1, 1, 0, 0, 0, -2, 1], -18), ([1, 1, 1, -2, 0, -1, 1], -9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, 0, -1, 0], -9), ([1, 2, 0, -1, -1, -1, 1], -9), ([1, 2, 0, -1, 0, -1, 0], -9)]

theorem source389_checked : normalize (row ![1, 0, -1, 0, -1, 1] ![0, 0, -1, 0, 1, 0] (0, -3)) = source389 := by
  decide +kernel

theorem source389_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source389 (momentValues f) = 0 := by
  rw [← source389_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source390 : Sparse := [([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, -1, 2, -1, 1, 0], 9), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, 0, -2, 1, -1, 1, 1], 9), ([0, 0, -1, 0, -1, 2, 0], 18), ([0, 0, -1, 1, -2, 1, 1], -9), ([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, -1, 1, 0, 1, -1], 9), ([0, 0, -1, 2, -2, 1, 0], 9), ([0, 0, 0, 1, -2, 1, 0], 9), ([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 0, 1, -1, 1, -1], 9), ([0, 1, -2, 1, -1, 1, 0], 9), ([0, 1, -1, 1, -2, 1, 0], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, 0, -2, 1, -1, 1, 1], 9), ([1, 0, -2, 1, 0, 1, 0], -9), ([1, 0, -2, 2, -1, 1, 0], 9), ([1, 0, -1, 0, -1, 2, 0], 18), ([1, 0, -1, 1, 0, 0, 0], 9), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 0, -1, 2, -1, 1, -1], 9), ([1, 0, 0, 1, -2, 1, 0], 9), ([1, 0, 0, 1, -1, 1, -1], 9), ([1, 1, -2, 1, -1, 1, 0], 9), ([1, 1, -1, 1, -2, 1, 0], 9), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, -1, 1, -1, 1, -1], -9)]

theorem source390_checked : normalize (row ![0, -1, 1, -1, 1, 0] ![0, 0, 1, 0, -1, 0] (3, 3)) = source390 := by
  decide +kernel

theorem source390_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source390 (momentValues f) = 0 := by
  rw [← source390_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source391 : Sparse := [([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 1, -2, 1, -1, 1], -9), ([0, 0, 1, -2, 2, -1, 0], 9), ([0, 0, 1, -1, 0, 0, 0], -9), ([0, 0, 1, -1, 1, 0, -1], 9), ([0, 0, 1, -1, 2, -1, -1], -9), ([0, 0, 2, -2, 1, -1, 0], -9), ([0, 0, 2, -1, 0, -1, 0], 9), ([0, 1, 0, -1, 1, -1, 0], -9), ([0, 1, 1, -2, 1, -1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 1, -1, 2, -1, 0], -9), ([1, -1, 2, -1, 1, -1, 0], -9), ([1, 0, 0, -1, 1, -1, 1], -9), ([1, 0, 0, -1, 2, -1, 0], -9), ([1, 0, 1, -2, 1, -1, 1], -9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 0, 1, -1, 0, 0, 0], -9), ([1, 0, 1, 0, 1, -2, 0], -18), ([1, 0, 2, -2, 1, -1, 0], -9), ([1, 0, 2, -1, 0, -1, 0], 9), ([1, 0, 2, -1, 1, -1, -1], -9), ([1, 1, 1, -1, 0, -1, 0], -9), ([1, 1, 1, -1, 1, -1, -1], -9)]

theorem source391_checked : normalize (row ![0, 1, -1, 1, -1, 0] ![0, 0, -1, 0, 1, 0] (0, -3)) = source391 := by
  decide +kernel

theorem source391_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source391 (momentValues f) = 0 := by
  rw [← source391_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
