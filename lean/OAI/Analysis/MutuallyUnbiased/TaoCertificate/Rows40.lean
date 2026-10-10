import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source320 : Sparse := [([0, -1, 1, -1, 1, 0, 0], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, 1, 0, -1], 9), ([0, -1, 2, -1, 1, 0, -1], 9), ([0, 0, 0, -1, 2, 0, -1], 18), ([0, 0, 1, -2, 1, 0, 0], 9), ([0, 0, 1, -2, 1, 1, -1], -9), ([0, 0, 1, -1, 0, 0, 0], 9), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 0, 1, -1, 1, 1, -2], 9), ([0, 0, 1, 0, 1, -1, -1], 9), ([0, 0, 2, -2, 1, 0, -1], 9), ([0, 1, 1, -2, 1, 0, -1], 9), ([0, 1, 1, -1, 1, 0, -2], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, 0, 0, -1, 2, 0, -1], 18), ([1, 0, 1, -2, 1, 0, 0], 9), ([1, 0, 1, -1, 1, -1, 0], 9), ([1, 0, 1, -1, 1, 1, -2], 9), ([1, 0, 1, 0, 0, 0, -1], 9), ([1, 0, 1, 0, 1, -1, -1], 9), ([1, 0, 1, 0, 1, 0, -2], -9), ([1, 0, 2, -1, 1, -1, -1], 9), ([1, 0, 2, -1, 1, 0, -2], 9), ([1, 1, 1, -2, 1, 0, -1], 9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, -1, 1, 0, -2], 9)]

theorem source320_checked : normalize (row ![0, 1, -1, 1, 0, -1] ![0, 1, 0, -1, 0, 0] (3, 3)) = source320 := by
  decide +kernel

theorem source320_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source320 (momentValues f) = 0 := by
  rw [← source320_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source321 : Sparse := [([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, 0, -2, 1, -1, 0, 2], -9), ([0, 0, -2, 1, -1, 1, 1], -9), ([0, 0, -2, 2, -1, 0, 1], 9), ([0, 0, -1, 0, -1, 0, 2], 9), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, -1, 1, 0, 0, 0], 9), ([0, 0, -1, 2, -1, -1, 1], -9), ([0, 1, -2, 1, -1, 0, 1], 9), ([0, 1, -1, 1, -1, 0, 0], -9), ([1, -1, -1, 1, -1, 0, 2], -9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 2, -1, 0, 1], -9), ([1, 0, -2, 1, -1, 0, 2], -9), ([1, 0, -2, 1, -1, 1, 1], -9), ([1, 0, -1, 0, -1, 0, 2], 9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, -1, 0, 0, 0, 1], -9), ([1, 0, -1, 1, -1, -1, 2], -9), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 0, -1, 2, -1, 0, 0], -9), ([1, 0, 0, 1, -2, 0, 1], -18), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, -1, 1, -1, -1, 1], -9)]

theorem source321_checked : normalize (row ![0, -1, 1, -1, 0, 1] ![0, -1, 0, 1, 0, 0] (0, -3)) = source321 := by
  decide +kernel

theorem source321_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source321 (momentValues f) = 0 := by
  rw [← source321_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source322 : Sparse := [([0, -1, 1, 0, 1, -1, 0], 9), ([0, -1, 2, 0, 1, -1, -1], -9), ([0, 0, 1, -1, 1, 0, -1], 9), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 0, 1, 1, 0, -1, -1], 9), ([0, 0, 1, 1, 1, -1, -2], -9), ([0, 0, 2, -1, 1, -1, -1], -9), ([0, 0, 2, 0, 1, -2, -1], 9), ([0, 0, 2, 0, 1, -1, -2], 9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 1, 0, 1, -2, -1], -9), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 2, 0, 1, -1, -1], -9), ([1, 0, 0, 0, 2, -1, -1], -18), ([1, 0, 1, -1, 1, -1, 0], -9), ([1, 0, 1, -1, 1, 0, -1], 9), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 0, 1, 0, 1, -2, 0], -9), ([1, 0, 1, 0, 1, 0, -2], -9), ([1, 0, 1, 1, 1, -2, -1], -9), ([1, 0, 2, -1, 1, -1, -1], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, 1, -1, -2], -9)]

theorem source322_checked : normalize (row ![0, 1, 0, 1, -1, -1] ![0, 1, 0, -1, 0, 0] (0, -3)) = source322 := by
  decide +kernel

theorem source322_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source322 (momentValues f) = 0 := by
  rw [← source322_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source323 : Sparse := [([0, -1, -1, 0, -1, 1, 2], 9), ([0, -1, -1, 0, -1, 2, 1], -9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, 0, -2, 0, -1, 1, 2], 9), ([0, 0, -2, 0, -1, 2, 1], 9), ([0, 0, -1, -1, -1, 1, 2], -9), ([0, 0, -1, -1, -1, 2, 1], 9), ([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, -1, 0, -1, 0, 2], 9), ([0, 0, -1, 0, -1, 2, 0], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, 0, 0, -2, 1, 1], 18), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, 0, -1, 0, 1], 9), ([1, -1, -1, 0, -1, 1, 2], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, 0, -2, 1, -1, 1, 1], 9), ([1, 0, -1, -1, -1, 2, 1], 9), ([1, 0, -1, 0, -1, 0, 2], 9), ([1, 0, -1, 0, -1, 2, 0], 9), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 0, 0, 0, -2, 1, 1], 18), ([1, 1, -2, 0, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 0, -1, 1, 0], -9)]

theorem source323_checked : normalize (row ![0, -1, 0, -1, 1, 1] ![0, -1, 0, 1, 0, 0] (3, 3)) = source323 := by
  decide +kernel

theorem source323_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source323 (momentValues f) = 0 := by
  rw [← source323_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source324 : Sparse := [([0, -2, -1, 1, 1, 1, 0], -9), ([0, -2, -1, 2, 1, 0, 0], 9), ([0, -1, -2, 2, 1, 0, 0], -9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 2, 1, -1, 0], -9), ([0, -1, -1, 2, 1, 0, -1], 9), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 1, 1, 0, -1], -9), ([0, 0, -2, 1, 1, 0, 0], 9), ([0, 0, -1, 1, 0, 0, 0], -9), ([1, -2, -1, 1, 1, 0, 1], -9), ([1, -2, 0, 1, 1, 0, 0], -9), ([1, -1, -2, 1, 1, 0, 1], -9), ([1, -1, -2, 1, 1, 1, 0], -9), ([1, -1, -2, 2, 1, 0, 0], -9), ([1, -1, -1, 0, 2, 0, 0], -18), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 2, 1, -1, 0], -9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, 0, -2, 1, 1, 0, 0], 9), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 0, -1, 1, 1, 0, -1], -9)]

theorem source324_checked : normalize (row ![-1, -1, 1, 1, 0, 0] ![0, 0, 1, -1, 0, 0] (0, -3)) = source324 := by
  decide +kernel

theorem source324_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source324 (momentValues f) = 0 := by
  rw [← source324_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source325 : Sparse := [([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, -1, -1, 1, 0], 9), ([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 1, 0, -1, 0, 0, 0], 9), ([0, 1, 1, -2, -1, 0, 1], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, 0, -1, 0], 9), ([0, 1, 1, 0, -2, 0, 0], 18), ([0, 1, 2, -1, -1, -1, 0], 9), ([0, 1, 2, -1, -1, 0, -1], 9), ([0, 2, 0, -1, -1, 0, 0], 9), ([0, 2, 1, -2, -1, 0, 0], 9), ([0, 2, 1, -1, -1, -1, 0], -9), ([0, 2, 1, -1, -1, 0, -1], 9), ([1, 0, 1, -1, -1, 0, 1], 9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 0, 1, -1, 0, 0, 0], 9), ([1, 0, 2, -1, -1, 0, 0], -9), ([1, 1, 0, -1, -1, 1, 0], 9), ([1, 1, 1, -2, -1, 1, 0], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, 0, -2, 0, 0], 18), ([1, 1, 2, -2, -1, 0, 0], 9), ([1, 1, 2, -1, -1, -1, 0], 9), ([1, 1, 2, -1, -1, 0, -1], 9), ([1, 2, 0, -1, -1, 0, 0], 9), ([1, 2, 1, -1, -1, 0, -1], 9)]

theorem source325_checked : normalize (row ![1, 1, -1, -1, 0, 0] ![0, 0, -1, 1, 0, 0] (3, 3)) = source325 := by
  decide +kernel

theorem source325_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source325 (momentValues f) = 0 := by
  rw [← source325_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source326 : Sparse := [([0, -2, 0, 1, 1, -1, 1], 9), ([0, -2, 1, 1, 1, -1, 0], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, -1, -1, 2, 1, -1, 0], 9), ([0, -1, 0, 0, 2, -1, 0], 18), ([0, -1, 0, 1, 0, -1, 1], 9), ([0, -1, 0, 1, 1, -2, 1], -9), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, -1, 0, 2, 1, -2, 0], 9), ([0, -1, 1, 1, 1, -2, 0], 9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 0, 1, 1, -2, 0], 9), ([0, 0, 0, 1, 1, -1, -1], 9), ([1, -2, 0, 1, 1, -1, 1], 9), ([1, -2, 0, 1, 1, 0, 0], -9), ([1, -2, 0, 2, 1, -1, 0], 9), ([1, -2, 1, 1, 1, -1, 0], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 1, 0, 0], 9), ([1, -1, 0, 0, 2, -1, 0], 18), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, -1, 0, 2, 1, -1, -1], 9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, -1, 1, 1, 1, -2, 0], 9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, 0, 0, 1, 1, -2, 0], 9), ([1, 0, 0, 1, 1, -1, -1], 9)]

theorem source326_checked : normalize (row ![-1, 0, 1, 1, -1, 0] ![0, 0, 1, -1, 0, 0] (3, 3)) = source326 := by
  decide +kernel

theorem source326_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source326 (momentValues f) = 0 := by
  rw [← source326_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source327 : Sparse := [([0, 0, 0, -1, 0, 1, 0], 9), ([0, 0, 1, -1, -1, 1, 0], -9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, 0, -2, -1, 1, 1], -9), ([0, 1, 0, -2, -1, 2, 0], 9), ([0, 1, 0, -1, -1, 2, -1], -9), ([0, 1, 0, -1, 0, 0, 0], -9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 1, 1, -2, -1, 1, 0], 9), ([0, 2, 0, -2, -1, 1, 0], -9), ([0, 2, 0, -1, -1, 0, 0], 9), ([1, 0, 0, -1, -1, 1, 1], -9), ([1, 0, 0, -1, -1, 2, 0], -9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 2, 0], -9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, 0, -2, -1, 1, 1], -9), ([1, 1, 0, -1, -1, 0, 1], -9), ([1, 1, 0, -1, 0, 0, 0], -9), ([1, 1, 0, 0, -2, 1, 0], -18), ([1, 1, 1, -1, -1, 0, 0], -9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 2, -1, -1, -1, 1, 0], -9), ([1, 2, 0, -2, -1, 1, 0], -9), ([1, 2, 0, -1, -1, 0, 0], 9), ([1, 2, 0, -1, -1, 1, -1], -9)]

theorem source327_checked : normalize (row ![1, 0, -1, -1, 1, 0] ![0, 0, -1, 1, 0, 0] (0, -3)) = source327 := by
  decide +kernel

theorem source327_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source327 (momentValues f) = 0 := by
  rw [← source327_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
