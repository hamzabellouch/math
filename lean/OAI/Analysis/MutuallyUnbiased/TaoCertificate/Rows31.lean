import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source248 : Sparse := [([0, 0, 0, 2, -1, 0, -1], 18), ([0, 1, -1, 1, -1, 0, 0], 9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, 0, 0, 0, 0, -1], 9), ([0, 1, 0, 1, -2, 1, -1], 9), ([0, 1, 0, 1, -1, -1, 0], 9), ([0, 1, 0, 1, -1, 1, -2], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 1, 0, 1, 0, 0, -2], 9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 1, 1, 1, -2, 0, -1], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, -1, 0, -2], -9), ([0, 2, 0, 1, -1, -1, -1], 9), ([0, 2, 0, 1, -1, 0, -2], 9), ([1, 0, 0, 2, -1, 0, -1], 18), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, 0, 0, -1, 0, 0], 9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 1, 0, 1, -2, 0, 0], -9), ([1, 1, 0, 1, -2, 1, -1], 9), ([1, 1, 0, 1, -1, -1, 0], 9), ([1, 1, 0, 1, -1, 1, -2], 9), ([1, 1, 0, 1, 0, 0, -2], 9), ([1, 1, 1, 1, -2, 0, -1], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 2, -1, 1, -1, 0, -1], 9), ([1, 2, 0, 1, -2, 0, -1], 9)]

theorem source248_checked : normalize (row ![1, 0, 1, -1, 0, -1] ![1, 0, -1, 0, 0, 0] (3, 3)) = source248 := by
  decide +kernel

theorem source248_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source248 (momentValues f) = 0 := by
  rw [← source248_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source249 : Sparse := [([0, -2, 0, -1, 1, 0, 2], 9), ([0, -2, 0, -1, 1, 1, 1], 9), ([0, -2, 0, -1, 2, 0, 1], -9), ([0, -2, 1, -1, 1, 0, 1], -9), ([0, -1, -1, -1, 1, 0, 2], -9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, 0, -1, 0, 1, 1], -9), ([0, -1, 0, -1, 2, 0, 0], 9), ([0, -1, 0, 0, 0, 0, 1], 9), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 1, -1, 1, -1, 1], 9), ([1, -2, 0, -1, 2, 0, 1], -9), ([1, -2, 1, -1, 1, 0, 1], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 2, 0, 1], -9), ([1, -1, 0, -1, 0, 0, 2], -9), ([1, -1, 0, -1, 1, -1, 2], -9), ([1, -1, 0, -1, 1, 1, 0], -9), ([1, -1, 0, -1, 2, -1, 1], -9), ([1, -1, 0, -1, 2, 0, 0], 9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, 0, 0, -2, 1, 0, 1], -18)]

theorem source249_checked : normalize (row ![-1, 0, -1, 1, 0, 1] ![-1, 0, 1, 0, 0, 0] (0, -3)) = source249 := by
  decide +kernel

theorem source249_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source249 (momentValues f) = 0 := by
  rw [← source249_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source250 : Sparse := [([0, 0, 0, 2, 0, -1, -1], 18), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 1, 0, 1, 0, -2, 0], 9), ([0, 1, 0, 1, 0, 0, -2], 9), ([0, 1, 0, 1, 1, -2, -1], -9), ([0, 1, 0, 1, 1, -1, -2], 9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, 0, -2, -1], 9), ([0, 1, 1, 1, 0, -1, -2], -9), ([0, 2, 0, 1, 0, -2, -1], 9), ([0, 2, 0, 1, 0, -1, -2], 9), ([1, 0, 0, 2, 0, -1, -1], 18), ([1, 1, -1, 1, 0, -1, 0], 9), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, 0, 0, -1, 0], 9), ([1, 1, 0, 0, 0, 0, -1], 9), ([1, 1, 0, 1, -1, -1, 0], -9), ([1, 1, 0, 1, -1, 0, -1], 9), ([1, 1, 0, 1, 0, -2, 0], 9), ([1, 1, 0, 1, 0, 0, -2], 9), ([1, 1, 0, 1, 1, -1, -2], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, 0, -2, -1], 9), ([1, 2, -1, 1, 0, -1, -1], 9), ([1, 2, 0, 1, -1, -1, -1], 9)]

theorem source250_checked : normalize (row ![1, 0, 1, 0, -1, -1] ![1, 0, -1, 0, 0, 0] (3, 3)) = source250 := by
  decide +kernel

theorem source250_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source250 (momentValues f) = 0 := by
  rw [← source250_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source251 : Sparse := [([0, -2, 0, -1, 0, 1, 2], 9), ([0, -2, 0, -1, 0, 2, 1], 9), ([0, -2, 0, -1, 1, 1, 1], -9), ([0, -2, 1, -1, 0, 1, 1], -9), ([0, -1, -1, -1, 0, 1, 2], -9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, 0, -1, -1, 2, 1], -9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, -1, 0, 0, 0, 0, 1], -9), ([0, -1, 0, 0, 0, 1, 0], -9), ([0, -1, 1, -1, 0, 0, 1], 9), ([1, -2, 0, -1, 1, 1, 1], -9), ([1, -2, 1, -1, 0, 1, 1], -9), ([1, -1, -1, -1, 0, 2, 1], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, 0, -1, -1, 1, 2], -9), ([1, -1, 0, -1, 0, 0, 2], -9), ([1, -1, 0, -1, 0, 2, 0], -9), ([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, -1, 0, 0, 0, 0, 1], -9), ([1, -1, 0, 0, 0, 1, 0], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, 0, 0, -2, 0, 1, 1], -18)]

theorem source251_checked : normalize (row ![-1, 0, -1, 0, 1, 1] ![-1, 0, 1, 0, 0, 0] (0, -3)) = source251 := by
  decide +kernel

theorem source251_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source251 (momentValues f) = 0 := by
  rw [← source251_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source252 : Sparse := [([0, -2, 1, 1, -1, 0, 1], 9), ([0, -2, 1, 1, -1, 1, 0], 9), ([0, -1, 0, 2, -1, 0, 0], 18), ([0, -1, 1, 0, -1, 1, 0], 9), ([0, -1, 1, 1, -2, 0, 1], 9), ([0, -1, 1, 1, -2, 1, 0], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, -1, 1, 1, 0, 0, -1], 9), ([0, -1, 2, 1, -2, 0, 0], 9), ([0, -1, 2, 1, -1, 0, -1], 9), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 0, 1, 1, -2, 0, 0], 9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 0, 1, 1, -1, 0, -1], -9), ([1, -2, 1, 1, -1, 0, 1], 9), ([1, -2, 1, 1, -1, 1, 0], 9), ([1, -2, 1, 1, 0, 0, 0], -9), ([1, -2, 2, 1, -1, 0, 0], 9), ([1, -1, 0, 2, -1, 0, 0], 18), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 1, 0, 0, 0, 0], 9), ([1, -1, 1, 1, -2, 0, 1], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 2, 1, -1, -1, 0], 9), ([1, 0, 1, 1, -2, 0, 0], 9), ([1, 0, 1, 1, -1, -1, 0], 9)]

theorem source252_checked : normalize (row ![-1, 1, 1, -1, 0, 0] ![0, 1, -1, 0, 0, 0] (3, 3)) = source252 := by
  decide +kernel

theorem source252_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source252 (momentValues f) = 0 := by
  rw [← source252_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source253 : Sparse := [([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 1, -2, -1, 1, 0, 1], 9), ([0, 1, -2, -1, 1, 1, 0], -9), ([0, 1, -2, -1, 2, 0, 0], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, -1, 2, -1, 0], -9), ([0, 1, -1, 0, 0, 0, 0], -9), ([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 2, -2, -1, 1, 0, 0], -9), ([0, 2, -1, -1, 0, 0, 0], 9), ([1, 0, -1, -1, 1, 1, 0], -9), ([1, 0, -1, -1, 2, 0, 0], -9), ([1, 1, -2, -1, 1, 1, 0], -9), ([1, 1, -1, -1, 0, 0, 1], -9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, -1, 2, 0, -1], -9), ([1, 1, -1, 0, 0, 0, 0], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, 0, -2, 1, 0, 0], -18), ([1, 2, -2, -1, 1, 0, 0], -9), ([1, 2, -1, -1, 0, 0, 0], 9), ([1, 2, -1, -1, 1, -1, 0], -9), ([1, 2, -1, -1, 1, 0, -1], -9)]

theorem source253_checked : normalize (row ![1, -1, -1, 1, 0, 0] ![0, -1, 1, 0, 0, 0] (0, -3)) = source253 := by
  decide +kernel

theorem source253_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source253 (momentValues f) = 0 := by
  rw [← source253_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source254 : Sparse := [([0, -2, 1, 1, 1, -1, 0], -9), ([0, -2, 2, 1, 0, -1, 0], 9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, -1, 1, 0, 0, 0, 0], -9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, -1, 1, 1, -1, 0, 0], 9), ([0, -1, 1, 1, 0, -2, 1], -9), ([0, -1, 2, 1, -1, -1, 0], -9), ([0, -1, 2, 1, 0, -2, 0], 9), ([0, -1, 2, 1, 0, -1, -1], -9), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 1, 1, 0, -1, -1], 9), ([1, -2, 1, 1, 0, -1, 1], -9), ([1, -2, 1, 1, 0, 0, 0], -9), ([1, -1, 0, 2, 0, -1, 0], -18), ([1, -1, 1, 0, 0, 0, 0], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 1, 1, -2, 0], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 2, 1, -1, -1, 0], -9), ([1, -1, 2, 1, 0, -1, -1], -9), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 1, 1, -1, -1, 0], -9), ([1, 0, 1, 1, 0, -2, 0], -9), ([1, 0, 1, 1, 0, -1, -1], 9)]

theorem source254_checked : normalize (row ![-1, 1, 1, 0, -1, 0] ![0, 1, -1, 0, 0, 0] (0, -3)) = source254 := by
  decide +kernel

theorem source254_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source254 (momentValues f) = 0 := by
  rw [← source254_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source255 : Sparse := [([0, 0, -1, -1, 0, 2, 0], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 1, -2, -1, 0, 2, 0], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, -1, 2, 0], 9), ([0, 1, -1, -1, 0, 0, 1], 9), ([0, 1, -1, -1, 0, 2, -1], -9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, -1, 1, 0], 9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, 0, -2, 0, 1, 0], 18), ([0, 2, -2, -1, 0, 1, 0], 9), ([0, 2, -1, -1, -1, 1, 0], -9), ([0, 2, -1, -1, 0, 0, 0], 9), ([0, 2, -1, -1, 0, 1, -1], 9), ([1, 0, -1, -1, 0, 1, 1], -9), ([1, 0, -1, -1, 0, 2, 0], 9), ([1, 0, -1, -1, 1, 1, 0], 9), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 1, -2, -1, 0, 1, 1], 9), ([1, 1, -2, -1, 1, 1, 0], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 2, 0], 9), ([1, 1, -1, -1, 0, 0, 1], 9), ([1, 1, -1, -1, 1, 0, 0], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, 0, 0, 0], 9), ([1, 1, 0, -2, 0, 1, 0], 18), ([1, 2, -1, -1, 0, 0, 0], 9), ([1, 2, -1, -1, 0, 1, -1], 9)]

theorem source255_checked : normalize (row ![1, -1, -1, 0, 1, 0] ![0, -1, 1, 0, 0, 0] (3, 3)) = source255 := by
  decide +kernel

theorem source255_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source255 (momentValues f) = 0 := by
  rw [← source255_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
