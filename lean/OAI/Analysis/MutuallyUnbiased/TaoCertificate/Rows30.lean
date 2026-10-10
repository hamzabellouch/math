import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source240 : Sparse := [([0, 1, -2, 1, -1, 1, 0], -9), ([0, 1, -1, 0, -1, 0, 1], 9), ([0, 1, -1, 0, -1, 1, 0], 9), ([0, 1, -1, 0, 0, 0, 0], -9), ([0, 1, -1, 1, -2, 0, 1], -9), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 1, 0, 0, -1, 0, 0], -9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 2, -2, 1, -1, 0, 0], 9), ([0, 2, -1, 1, -2, 0, 0], 9), ([0, 2, -1, 1, -1, -1, 0], -9), ([0, 2, -1, 1, -1, 0, -1], -9), ([1, 0, -1, 2, -1, 0, 0], -18), ([1, 1, -2, 1, -1, 0, 1], -9), ([1, 1, -2, 1, 0, 0, 0], -9), ([1, 1, -1, 0, 0, 0, 0], -9), ([1, 1, -1, 1, -2, 1, 0], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, -1, 0], 9), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, 0, 0, -1, 0, 0], -9), ([1, 1, 0, 1, -2, 0, 0], -9), ([1, 1, 0, 1, -1, -1, 0], -9), ([1, 1, 0, 1, -1, 0, -1], 9), ([1, 2, -1, 1, -1, -1, 0], -9), ([1, 2, -1, 1, -1, 0, -1], -9)]

theorem source240_checked : normalize (row ![1, -1, 1, -1, 0, 0] ![1, 0, -1, 0, 0, 0] (0, -3)) = source240 := by
  decide +kernel

theorem source240_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source240 (momentValues f) = 0 := by
  rw [← source240_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source241 : Sparse := [([0, -2, 1, -1, 2, 0, 0], 9), ([0, -2, 2, -1, 1, 0, 0], 9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 0, -1, 2, 0, 0], 9), ([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, -1, 2, -1, 0], 9), ([0, -1, 1, -1, 2, 0, -1], -9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, -1, 1, 0, 1, 0, -1], 9), ([0, -1, 2, -1, 0, 0, 0], 9), ([0, -1, 2, -1, 1, -1, 0], -9), ([0, -1, 2, -1, 1, 0, -1], 9), ([0, 0, 1, -2, 1, 0, 0], 18), ([1, -2, 1, -1, 1, 0, 1], 9), ([1, -2, 1, -1, 1, 1, 0], 9), ([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 0, -1, 1, 1, 0], 9), ([1, -1, 0, -1, 2, 0, 0], 9), ([1, -1, 0, 0, 1, 0, 0], 9), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, -1, 2, -1, 0], 9), ([1, -1, 1, 0, 0, 0, 0], 9), ([1, -1, 2, -1, 0, 0, 0], 9), ([1, -1, 2, -1, 1, 0, -1], 9), ([1, 0, 1, -2, 1, 0, 0], 18)]

theorem source241_checked : normalize (row ![-1, 1, -1, 1, 0, 0] ![-1, 0, 1, 0, 0, 0] (3, 3)) = source241 := by
  decide +kernel

theorem source241_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source241 (momentValues f) = 0 := by
  rw [← source241_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source242 : Sparse := [([0, 0, -1, 2, 0, -1, 0], 18), ([0, 1, -2, 1, 0, -1, 1], 9), ([0, 1, -2, 1, 1, -1, 0], 9), ([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, -1, 1, -1, 0, 0], 9), ([0, 1, -1, 1, 0, -2, 1], 9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, -1, 1, 1, -2, 0], -9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, 0, 0, -1, 0], 9), ([0, 1, 0, 1, -1, -1, 0], 9), ([0, 1, 0, 1, 0, -2, 0], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 2, -1, 1, 0, -2, 0], 9), ([0, 2, -1, 1, 0, -1, -1], 9), ([1, 0, -1, 2, 0, -1, 0], 18), ([1, 1, -2, 1, 0, -1, 1], 9), ([1, 1, -2, 1, 0, 0, 0], -9), ([1, 1, -2, 1, 1, -1, 0], 9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, -1, 0, 0, 0, 0], 9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, -1, 1, 0, -2, 1], 9), ([1, 1, -1, 1, 0, 0, -1], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, 1, -1, -1, 0], 9), ([1, 1, 0, 1, 0, -2, 0], 9), ([1, 2, -2, 1, 0, -1, 0], 9), ([1, 2, -1, 1, -1, -1, 0], 9)]

theorem source242_checked : normalize (row ![1, -1, 1, 0, -1, 0] ![1, 0, -1, 0, 0, 0] (3, 3)) = source242 := by
  decide +kernel

theorem source242_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source242 (momentValues f) = 0 := by
  rw [← source242_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source243 : Sparse := [([0, -2, 1, -1, 0, 1, 1], 9), ([0, -2, 1, -1, 0, 2, 0], 9), ([0, -2, 1, -1, 1, 1, 0], -9), ([0, -2, 2, -1, 0, 1, 0], -9), ([0, -1, 0, -1, 0, 1, 1], -9), ([0, -1, 0, 0, 0, 1, 0], 9), ([0, -1, 1, -1, -1, 2, 0], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, -1, 1, 0], 9), ([0, -1, 1, 0, 0, 0, 0], -9), ([0, -1, 1, 0, 0, 1, -1], -9), ([0, -1, 2, -1, 0, 0, 0], 9), ([1, -2, 1, -1, 1, 1, 0], -9), ([1, -2, 2, -1, 0, 1, 0], -9), ([1, -1, 0, -1, 0, 2, 0], -9), ([1, -1, 0, -1, 1, 1, 0], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, -1, 0, 2, -1], -9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, 0, 0, 0], -9), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 2, -1, -1, 1, 0], -9), ([1, -1, 2, -1, 0, 0, 0], 9), ([1, -1, 2, -1, 0, 1, -1], -9), ([1, 0, 1, -2, 0, 1, 0], -18)]

theorem source243_checked : normalize (row ![-1, 1, -1, 0, 1, 0] ![-1, 0, 1, 0, 0, 0] (0, -3)) = source243 := by
  decide +kernel

theorem source243_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source243 (momentValues f) = 0 := by
  rw [← source243_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source244 : Sparse := [([0, 1, -2, 1, 0, 1, -1], -9), ([0, 1, -1, 0, 0, 0, 0], 9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 1, -1, 1, -1, 0, 0], -9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, 0, 0, 0, -1], -9), ([0, 1, 0, 1, 0, 0, -2], 9), ([0, 2, -2, 1, 0, 0, -1], 9), ([0, 2, -1, 1, -1, 0, -1], 9), ([0, 2, -1, 1, 0, -1, -1], -9), ([0, 2, -1, 1, 0, 0, -2], -9), ([1, 0, -1, 2, 0, 0, -1], -18), ([1, 1, -2, 1, 0, 0, 0], -9), ([1, 1, -2, 1, 1, 0, -1], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, -1, 1, 0, 1, -2], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 1, 1, 0, -2], -9), ([1, 1, 0, 0, 0, 0, -1], -9), ([1, 1, 0, 1, -1, 0, -1], -9), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 1, 0, 1, 0, 0, -2], 9), ([1, 2, -1, 1, 0, -1, -1], -9), ([1, 2, -1, 1, 0, 0, -2], -9)]

theorem source244_checked : normalize (row ![1, -1, 1, 0, 0, -1] ![1, 0, -1, 0, 0, 0] (0, -3)) = source244 := by
  decide +kernel

theorem source244_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source244 (momentValues f) = 0 := by
  rw [← source244_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source245 : Sparse := [([0, -2, 1, -1, 1, 0, 1], 9), ([0, -2, 2, -1, 0, 0, 1], 9), ([0, -1, 0, -1, 0, 1, 1], 9), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 1, -1, -1, 0, 2], 9), ([0, -1, 1, -1, 0, -1, 2], 9), ([0, -1, 1, -1, 0, 1, 0], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, -1, 1, 0, 0, 0, 0], 9), ([0, -1, 2, -1, -1, 0, 1], 9), ([0, -1, 2, -1, 0, -1, 1], -9), ([0, -1, 2, -1, 0, 0, 0], 9), ([0, 0, 1, -2, 0, 0, 1], 18), ([1, -2, 1, -1, 0, 0, 2], 9), ([1, -2, 1, -1, 0, 1, 1], 9), ([1, -1, 0, -1, 0, 0, 2], -9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 0, -1, 1, 0, 1], 9), ([1, -1, 0, 0, 0, 0, 1], 9), ([1, -1, 1, -1, -1, 0, 2], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 0, -1, 2], 9), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 2, -1, -1, 0, 1], 9), ([1, -1, 2, -1, 0, 0, 0], 9), ([1, 0, 1, -2, 0, 0, 1], 18)]

theorem source245_checked : normalize (row ![-1, 1, -1, 0, 0, 1] ![-1, 0, 1, 0, 0, 0] (3, 3)) = source245 := by
  decide +kernel

theorem source245_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source245 (momentValues f) = 0 := by
  rw [← source245_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source246 : Sparse := [([0, 1, -1, 1, -1, 0, 0], -9), ([0, 1, 0, 0, -1, -1, 1], 9), ([0, 1, 0, 0, -1, 0, 0], 9), ([0, 1, 0, 0, 0, -1, 0], -9), ([0, 1, 0, 1, -2, -1, 1], -9), ([0, 1, 0, 1, 0, -2, 0], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 2, -1, 1, -1, -1, 0], 9), ([0, 2, 0, 1, -2, -1, 0], 9), ([0, 2, 0, 1, -1, -2, 0], -9), ([0, 2, 0, 1, -1, -1, -1], -9), ([1, 0, 0, 2, -1, -1, 0], -18), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, 0, 0, 0, -1, 0], -9), ([1, 1, 0, 1, -2, 0, 0], -9), ([1, 1, 0, 1, -1, -2, 1], -9), ([1, 1, 0, 1, -1, 0, -1], -9), ([1, 1, 0, 1, 0, -2, 0], 9), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 1, 1, 1, -2, -1, 0], -9), ([1, 1, 1, 1, -1, -2, 0], -9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 2, 0, 1, -1, -2, 0], -9), ([1, 2, 0, 1, -1, -1, -1], -9)]

theorem source246_checked : normalize (row ![1, 0, 1, -1, -1, 0] ![1, 0, -1, 0, 0, 0] (0, -3)) = source246 := by
  decide +kernel

theorem source246_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source246 (momentValues f) = 0 := by
  rw [← source246_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source247 : Sparse := [([0, -2, 0, -1, 2, 1, 0], 9), ([0, -2, 1, -1, 1, 1, 0], 9), ([0, -1, -1, -1, 1, 2, 0], 9), ([0, -1, -1, -1, 2, 1, 0], 9), ([0, -1, 0, -1, 0, 1, 1], 9), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 0, -1, 1, 2, -1], 9), ([0, -1, 0, -1, 2, 0, 0], 9), ([0, -1, 0, -1, 2, 1, -1], -9), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, -1, 0, 0, 1, 1, -1], 9), ([0, -1, 1, -1, 0, 1, 0], 9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, 0, 0, -2, 1, 1, 0], 18), ([1, -2, 0, -1, 1, 1, 1], 9), ([1, -2, 0, -1, 1, 2, 0], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 1, 2, 0], 9), ([1, -1, -1, -1, 2, 1, 0], 9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 0, -1, 0, 2, 0], -9), ([1, -1, 0, -1, 1, 0, 1], 9), ([1, -1, 0, -1, 1, 2, -1], 9), ([1, -1, 0, -1, 2, 0, 0], 9), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, 0, 0, -2, 1, 1, 0], 18)]

theorem source247_checked : normalize (row ![-1, 0, -1, 1, 1, 0] ![-1, 0, 1, 0, 0, 0] (3, 3)) = source247 := by
  decide +kernel

theorem source247_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source247 (momentValues f) = 0 := by
  rw [← source247_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
