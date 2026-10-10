import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source304 : Sparse := [([0, 0, -1, 0, 2, 0, -1], 18), ([0, 1, -2, 0, 1, 0, 0], 9), ([0, 1, -2, 0, 1, 1, -1], 9), ([0, 1, -2, 1, 1, 0, -1], -9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, -1, 0, 1, 1, -2], -9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, -1, 1, 1, 0, -2], 9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 1, 0, 0, 1, 0, -2], 9), ([0, 2, -2, 0, 1, 0, -1], 9), ([0, 2, -1, 0, 1, 0, -2], 9), ([1, 0, -1, 0, 2, 0, -1], 18), ([1, 1, -2, 0, 1, 0, 0], 9), ([1, 1, -2, 0, 1, 1, -1], 9), ([1, 1, -1, -1, 1, 0, 0], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, 0, 0, 0], 9), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 1, 1, 0, -2], 9), ([1, 1, 0, -1, 1, 0, -1], 9), ([1, 1, 0, 0, 0, 0, -1], 9), ([1, 1, 0, 0, 1, -1, -1], -9), ([1, 1, 0, 0, 1, 0, -2], 9), ([1, 2, -1, -1, 1, 0, -1], 9), ([1, 2, -1, 0, 1, -1, -1], 9)]

theorem source304_checked : normalize (row ![1, -1, 0, 1, 0, -1] ![1, 0, 0, -1, 0, 0] (3, 3)) = source304 := by
  decide +kernel

theorem source304_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source304 (momentValues f) = 0 := by
  rw [← source304_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source305 : Sparse := [([0, -2, 1, 0, -1, 0, 2], 9), ([0, -2, 1, 0, -1, 1, 1], -9), ([0, -2, 1, 1, -1, 0, 1], -9), ([0, -2, 2, 0, -1, 0, 1], 9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, -1, 0, 0, 0, 0, 1], -9), ([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 1, 0, -1, -1, 2], -9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, -1, 1, 0, 0, 0, 0], -9), ([0, -1, 1, 1, -1, 0, 0], 9), ([0, -1, 2, -1, -1, 0, 1], -9), ([1, -2, 1, 0, -1, 1, 1], -9), ([1, -2, 1, 1, -1, 0, 1], -9), ([1, -1, 0, 0, -1, 0, 2], -9), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, -1, 0, 0, 0, 0, 1], -9), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 1, -1, -1, 0, 2], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 1, 0, 0, 0, 0], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, -1, 2, 0, -1, -1, 1], -9), ([1, -1, 2, 0, -1, 0, 0], -9), ([1, 0, 1, 0, -2, 0, 1], -18)]

theorem source305_checked : normalize (row ![-1, 1, 0, -1, 0, 1] ![-1, 0, 0, 1, 0, 0] (0, -3)) = source305 := by
  decide +kernel

theorem source305_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source305 (momentValues f) = 0 := by
  rw [← source305_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source306 : Sparse := [([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, 0, -2, 1, -1, 1], -9), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 1, 0, -1, 0, 0, 0], -9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 1, 0, 0, 0, -1, 0], -9), ([0, 1, 1, -1, 0, -1, 0], 9), ([0, 1, 1, -1, 1, -2, 0], -9), ([0, 2, -1, -1, 1, -1, 0], -9), ([0, 2, 0, -2, 1, -1, 0], 9), ([0, 2, 0, -1, 1, -2, 0], 9), ([0, 2, 0, -1, 1, -1, -1], -9), ([1, 0, 0, -1, 2, -1, 0], -18), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 1, 0, 0], -9), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, 0, -2, 1, 0, 0], -9), ([1, 1, 0, -1, 0, 0, 0], -9), ([1, 1, 0, -1, 1, -2, 1], -9), ([1, 1, 0, -1, 1, 0, -1], 9), ([1, 1, 0, 0, 0, -1, 0], -9), ([1, 1, 0, 0, 1, -2, 0], -9), ([1, 1, 0, 0, 1, -1, -1], -9), ([1, 1, 1, -2, 1, -1, 0], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 2, -1, -1, 1, -1, 0], -9), ([1, 2, 0, -1, 1, -1, -1], -9)]

theorem source306_checked : normalize (row ![1, 0, -1, 1, -1, 0] ![1, 0, 0, -1, 0, 0] (0, -3)) = source306 := by
  decide +kernel

theorem source306_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source306 (momentValues f) = 0 := by
  rw [← source306_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source307 : Sparse := [([0, -2, 0, 1, -1, 2, 0], 9), ([0, -2, 0, 2, -1, 1, 0], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, -1, 2, 0], -9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, -1, 2, -1, 1, 0], 9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, -1, 0, 0, -1, 2, 0], 9), ([0, -1, 0, 1, -1, 2, -1], 9), ([0, -1, 0, 1, 0, 1, -1], 9), ([0, -1, 0, 2, -1, 0, 0], 9), ([0, -1, 0, 2, -1, 1, -1], -9), ([0, -1, 1, 1, -1, 0, 0], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, 0, 0, 1, -2, 1, 0], 18), ([1, -2, 0, 1, -1, 1, 1], 9), ([1, -2, 1, 1, -1, 1, 0], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 2, -1, 1, 0], 9), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, -1, 0, 0, -1, 2, 0], 9), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, -1, 2, -1], 9), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, -1, 0, 2, -1, 0, 0], 9), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, 0, 0, 1, -2, 1, 0], 18)]

theorem source307_checked : normalize (row ![-1, 0, 1, -1, 1, 0] ![-1, 0, 0, 1, 0, 0] (3, 3)) = source307 := by
  decide +kernel

theorem source307_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source307 (momentValues f) = 0 := by
  rw [← source307_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source308 : Sparse := [([0, 0, 0, -1, 2, 0, -1], 18), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 1, 0, -2, 1, 1, -1], 9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 1, 0, -1, 1, -1, 0], 9), ([0, 1, 0, -1, 1, 1, -2], -9), ([0, 1, 0, 0, 0, 0, -1], 9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 1, 0, 0, 1, 0, -2], 9), ([0, 1, 1, -2, 1, 0, -1], 9), ([0, 1, 1, -1, 1, 0, -2], 9), ([0, 2, -1, -1, 1, 0, -1], 9), ([0, 2, 0, -1, 1, 0, -2], 9), ([1, 0, 0, -1, 2, 0, -1], 18), ([1, 1, -1, -1, 1, 0, 0], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, 0, -2, 1, 0, 0], -9), ([1, 1, 0, -2, 1, 1, -1], 9), ([1, 1, 0, -1, 0, 0, 0], 9), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 1, 0, 0, 1, -1, -1], 9), ([1, 1, 0, 0, 1, 0, -2], 9), ([1, 1, 1, -2, 1, 0, -1], 9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, -1, 1, 0, -2], 9), ([1, 2, 0, -2, 1, 0, -1], 9), ([1, 2, 0, -1, 1, -1, -1], 9)]

theorem source308_checked : normalize (row ![1, 0, -1, 1, 0, -1] ![1, 0, 0, -1, 0, 0] (3, 3)) = source308 := by
  decide +kernel

theorem source308_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source308 (momentValues f) = 0 := by
  rw [← source308_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source309 : Sparse := [([0, -2, 0, 1, -1, 0, 2], 9), ([0, -2, 0, 1, -1, 1, 1], -9), ([0, -2, 0, 2, -1, 0, 1], -9), ([0, -2, 1, 1, -1, 0, 1], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, 0, 0, 0, 0, 1], 9), ([0, -1, 0, 1, -1, -1, 2], -9), ([0, -1, 0, 1, 0, -1, 1], 9), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 2, -1, 0, 0], 9), ([0, -1, 1, 0, -1, 0, 1], -9), ([1, -2, 0, 1, -1, 1, 1], -9), ([1, -2, 0, 2, -1, 0, 1], -9), ([1, -1, -1, 1, -1, 0, 2], -9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 2, -1, 0, 1], -9), ([1, -1, 0, 0, -1, 0, 2], -9), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, -1, 0, 2, -1, -1, 1], -9), ([1, -1, 0, 2, -1, 0, 0], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, 0, 0, 1, -2, 0, 1], -18)]

theorem source309_checked : normalize (row ![-1, 0, 1, -1, 0, 1] ![-1, 0, 0, 1, 0, 0] (0, -3)) = source309 := by
  decide +kernel

theorem source309_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source309 (momentValues f) = 0 := by
  rw [← source309_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source310 : Sparse := [([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, -1, 1, -1, 0], -9), ([0, 1, 0, 0, 0, -1, 0], 9), ([0, 1, 0, 0, 0, 0, -1], -9), ([0, 1, 0, 0, 1, 0, -2], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 1, 0, 1, -2, -1], -9), ([0, 2, -1, 0, 1, -1, -1], -9), ([0, 2, 0, -1, 1, -1, -1], 9), ([0, 2, 0, 0, 1, -2, -1], 9), ([0, 2, 0, 0, 1, -1, -2], -9), ([1, 0, 0, 0, 2, -1, -1], -18), ([1, 1, -1, 0, 1, -1, 0], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, -1, 1, 0, -1], -9), ([1, 1, 0, 0, 0, 0, -1], -9), ([1, 1, 0, 0, 1, -2, 0], -9), ([1, 1, 0, 0, 1, 0, -2], 9), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 1, 0, 1, 1, -2, -1], -9), ([1, 1, 0, 1, 1, -1, -2], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, 1, -1, -2], -9), ([1, 2, -1, 0, 1, -1, -1], -9), ([1, 2, 0, 0, 1, -1, -2], -9)]

theorem source310_checked : normalize (row ![1, 0, 0, 1, -1, -1] ![1, 0, 0, -1, 0, 0] (0, -3)) = source310 := by
  decide +kernel

theorem source310_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source310 (momentValues f) = 0 := by
  rw [← source310_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source311 : Sparse := [([0, -2, 0, 0, -1, 2, 1], 9), ([0, -2, 0, 1, -1, 1, 1], 9), ([0, -1, -1, 0, -1, 1, 2], 9), ([0, -1, -1, 0, -1, 2, 1], -9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, 0, -1, -1, 1, 2], 9), ([0, -1, 0, -1, -1, 2, 1], 9), ([0, -1, 0, 0, -1, 2, 0], 9), ([0, -1, 0, 0, 0, 1, 0], 9), ([0, -1, 0, 1, -1, 0, 1], 9), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 0, -1, 1, 0], 9), ([0, 0, 0, 0, -2, 1, 1], 18), ([1, -2, 0, 0, -1, 1, 2], 9), ([1, -2, 1, 0, -1, 1, 1], 9), ([1, -1, -1, 0, -1, 1, 2], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, 0, -1, -1, 1, 2], 9), ([1, -1, 0, -1, -1, 2, 1], 9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 0, 0, -1, 0, 2], -9), ([1, -1, 0, 0, -1, 2, 0], 9), ([1, -1, 0, 0, 0, 0, 1], 9), ([1, -1, 0, 1, -1, 0, 1], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, 0, 0, 0, -2, 1, 1], 18)]

theorem source311_checked : normalize (row ![-1, 0, 0, -1, 1, 1] ![-1, 0, 0, 1, 0, 0] (3, 3)) = source311 := by
  decide +kernel

theorem source311_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source311 (momentValues f) = 0 := by
  rw [← source311_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
