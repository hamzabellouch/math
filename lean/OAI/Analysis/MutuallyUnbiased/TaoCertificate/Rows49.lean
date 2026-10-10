import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source392 : Sparse := [([0, -1, -1, 2, 0, 1, -1], -9), ([0, -1, 0, 1, 0, 1, -1], 9), ([0, 0, -2, 1, 1, 1, -1], -9), ([0, 0, -2, 2, 0, 1, -1], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 0, -1, 1, 1, 0, -1], 9), ([0, 0, -1, 2, -1, 1, -1], -9), ([0, 0, -1, 2, 0, 1, -2], 9), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, -1, 1, 0, 1, -2], -9), ([1, -1, -1, 1, 0, 1, 0], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 2, 0, 1, -1], -9), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, 0, -2, 1, 0, 1, 0], -9), ([1, 0, -1, 0, 0, 2, -1], -18), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, 1, -2], -9), ([1, 0, -1, 2, -1, 1, -1], -9), ([1, 0, 0, 1, -1, 1, -1], -9), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 1, 0, 1, -2], -9), ([1, 1, -2, 1, 0, 1, -1], -9), ([1, 1, -1, 1, -1, 1, -1], -9)]

theorem source392_checked : normalize (row ![0, -1, 1, 0, 1, -1] ![0, 0, 1, 0, -1, 0] (0, -3)) = source392 := by
  decide +kernel

theorem source392_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source392 (momentValues f) = 0 := by
  rw [← source392_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source393 : Sparse := [([0, -1, 1, -1, 0, -1, 2], -9), ([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 2, -1, 0, -1, 1], 9), ([0, 0, 0, -1, 0, -1, 2], 9), ([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 1, -2, 0, -1, 2], 9), ([0, 0, 1, -1, -1, -1, 2], 9), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, 0, 0, -2, 1], 18), ([0, 0, 2, -2, 0, -1, 1], 9), ([0, 0, 2, -1, -1, -1, 1], -9), ([0, 0, 2, -1, 0, -1, 0], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, 0, -1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 2, -1, 0, -1, 1], 9), ([1, 0, 0, -1, 0, -1, 2], 9), ([1, 0, 0, -1, 0, 0, 1], 9), ([1, 0, 0, -1, 1, -1, 1], 9), ([1, 0, 1, -2, 1, -1, 1], 9), ([1, 0, 1, -1, -1, -1, 2], 9), ([1, 0, 1, -1, 0, 0, 0], 9), ([1, 0, 1, -1, 1, -1, 0], -9), ([1, 0, 1, 0, 0, -2, 1], 18), ([1, 0, 2, -1, 0, -1, 0], 9), ([1, 1, 0, -1, 0, -1, 1], -9), ([1, 1, 1, -2, 0, -1, 1], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, 0, -1, 0], 9)]

theorem source393_checked : normalize (row ![0, 1, -1, 0, -1, 1] ![0, 0, -1, 0, 1, 0] (3, 3)) = source393 := by
  decide +kernel

theorem source393_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source393 (momentValues f) = 0 := by
  rw [← source393_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source394 : Sparse := [([0, -1, 0, 2, -1, 1, -1], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, -1, 2, -1, 1, -1], 9), ([0, 0, 0, 1, -2, 1, 0], 9), ([0, 0, 0, 1, -1, 0, 0], -9), ([0, 0, 0, 1, 0, 0, -1], 9), ([0, 0, 0, 2, -2, 1, -1], -9), ([0, 0, 0, 2, -1, 1, -2], 9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 1, 0, 1, -1, 1, -2], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, -1, 0, 2, -1, 1, -1], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 0, 0, 0, -1, 2, -1], -18), ([1, 0, 0, 1, -2, 1, 0], 9), ([1, 0, 0, 1, -1, 0, 0], -9), ([1, 0, 0, 1, 0, 1, -2], -9), ([1, 0, 0, 2, -2, 1, -1], -9), ([1, 0, 1, 1, -2, 1, -1], -9), ([1, 0, 1, 1, -1, 0, -1], -9), ([1, 0, 1, 1, -1, 1, -2], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, 0, 1, -2, 1, -1], -9)]

theorem source394_checked : normalize (row ![0, 0, 1, -1, 1, -1] ![0, 0, 1, 0, -1, 0] (0, -3)) = source394 := by
  decide +kernel

theorem source394_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source394 (momentValues f) = 0 := by
  rw [← source394_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source395 : Sparse := [([0, -1, 0, -1, 1, -1, 2], -9), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 0, -1, 2, -1, 1], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, 0, -1, -1, 1, -1, 2], 9), ([0, 0, -1, -1, 2, -1, 1], 9), ([0, 0, 0, -2, 1, -1, 2], 9), ([0, 0, 0, -1, 0, -1, 2], 9), ([0, 0, 0, -1, 0, 0, 1], 9), ([0, 0, 0, 0, 1, -2, 1], 18), ([0, 0, 1, -2, 1, -1, 1], 9), ([0, 0, 1, -1, 0, -1, 1], -9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 1, 0, -1, 1, -1, 0], 9), ([1, -1, 0, -1, 2, -1, 1], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, 0, -1, -1, 1, -1, 2], 9), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, -1, -1, 2, -1, 1], 9), ([1, 0, 0, -2, 2, -1, 1], 9), ([1, 0, 0, -1, 0, -1, 2], 9), ([1, 0, 0, -1, 1, 0, 0], 9), ([1, 0, 0, -1, 2, -1, 0], -9), ([1, 0, 0, 0, 1, -2, 1], 18), ([1, 0, 1, -1, 1, -1, 0], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, 0, -2, 1, -1, 1], 9), ([1, 1, 0, -1, 0, -1, 1], 9), ([1, 1, 0, -1, 1, -1, 0], 9)]

theorem source395_checked : normalize (row ![0, 0, -1, 1, -1, 1] ![0, 0, -1, 0, 1, 0] (3, 3)) = source395 := by
  decide +kernel

theorem source395_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source395 (momentValues f) = 0 := by
  rw [← source395_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source396 : Sparse := [([0, -2, -1, 0, 1, 1, 1], -9), ([0, -2, -1, 0, 2, 1, 0], 9), ([0, -1, -2, 0, 2, 1, 0], 9), ([0, -1, -2, 1, 1, 1, 0], -9), ([0, -1, -1, -1, 2, 1, 0], -9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, -1, 0, 2, 1, -1], -9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 1, 1, -1], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, -1, 0, 1, 0, 0], -9), ([1, -2, -1, 1, 1, 1, 0], -9), ([1, -2, 0, 0, 1, 1, 0], -9), ([1, -1, -2, 0, 1, 1, 1], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 2, 1, 0], -9), ([1, -1, -1, 0, 0, 2, 0], -18), ([1, -1, -1, 0, 2, 1, -1], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, 0, -1, 1, 1, 0], -9), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, 0, -2, 0, 1, 1, 0], -9), ([1, 0, -1, -1, 1, 1, 0], 9), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, -1, 0, 1, 1, -1], -9)]

theorem source396_checked : normalize (row ![-1, -1, 0, 1, 1, 0] ![0, 0, 0, 1, -1, 0] (0, -3)) = source396 := by
  decide +kernel

theorem source396_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source396 (momentValues f) = 0 := by
  rw [← source396_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source397 : Sparse := [([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 2, 0, -1, -1, 0], 9), ([0, 1, 0, 1, -1, -1, 0], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, -1, 0, 0], 9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 1, 1, 0, 0, -2, 0], 18), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 2, -1, -1, -1, 0], -9), ([0, 1, 2, 0, -2, -1, 0], 9), ([0, 1, 2, 0, -1, -1, -1], 9), ([0, 2, 0, 0, -1, -1, 0], 9), ([0, 2, 1, -1, -1, -1, 0], 9), ([0, 2, 1, 0, -2, -1, 0], 9), ([0, 2, 1, 0, -1, -1, -1], -9), ([1, 0, 1, 0, -1, -1, 1], 9), ([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 1, 1, -1, -1, 0], -9), ([1, 0, 2, 0, -1, -1, 0], 9), ([1, 1, 0, 0, -1, -1, 1], -9), ([1, 1, 0, 0, -1, 0, 0], 9), ([1, 1, 0, 1, -1, -1, 0], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, 0, -2, -1, 1], 9), ([1, 1, 1, 0, 0, -2, 0], 18), ([1, 1, 1, 1, -2, -1, 0], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 2, 0, -1, -1, -1], 9), ([1, 2, 0, 0, -1, -1, 0], 9), ([1, 2, 1, -1, -1, -1, 0], 9)]

theorem source397_checked : normalize (row ![1, 1, 0, -1, -1, 0] ![0, 0, 0, -1, 1, 0] (3, 3)) = source397 := by
  decide +kernel

theorem source397_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source397 (momentValues f) = 0 := by
  rw [← source397_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source398 : Sparse := [([0, -2, 0, -1, 1, 1, 1], -9), ([0, -2, 0, -1, 2, 1, 0], 9), ([0, -1, -1, -1, 2, 1, 0], 9), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, 0, -2, 2, 1, 0], -9), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 0, -1, 2, 1, -1], -9), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, 0, 0, -2, 1, 1, 0], 9), ([0, 0, 0, -1, 1, 0, 0], -9), ([1, -2, 0, 0, 1, 1, 0], -9), ([1, -2, 1, -1, 1, 1, 0], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, 0, -2, 1, 1, 1], -9), ([1, -1, 0, -2, 2, 1, 0], -9), ([1, -1, 0, -1, 0, 2, 0], -18), ([1, -1, 0, -1, 2, 1, -1], -9), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, -1, 1, -2, 1, 1, 0], -9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, 0, -1, -1, 1, 1, 0], -9), ([1, 0, 0, -2, 1, 1, 0], 9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 0, 0, -1, 1, 1, -1], -9)]

theorem source398_checked : normalize (row ![-1, 0, -1, 1, 1, 0] ![0, 0, 0, 1, -1, 0] (0, -3)) = source398 := by
  decide +kernel

theorem source398_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source398 (momentValues f) = 0 := by
  rw [← source398_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source399 : Sparse := [([0, 0, 0, 1, -1, -1, 1], 9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 1, -1, 2, -1, -1, 0], 9), ([0, 1, 0, 0, -1, -1, 1], 9), ([0, 1, 0, 0, -1, 0, 0], 9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 1, 0, 1, 0, -2, 0], 18), ([0, 1, 0, 2, -1, -1, -1], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 1, 1, 1, -2, -1, 0], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 2, -1, 1, -1, -1, 0], 9), ([0, 2, 0, 0, -1, -1, 0], 9), ([0, 2, 0, 1, -2, -1, 0], 9), ([0, 2, 0, 1, -1, -1, -1], -9), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 0, 0, 2, -1, -1, 0], -9), ([1, 0, 1, 1, -1, -1, 0], 9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, -1, 2, -1, -1, 0], 9), ([1, 1, 0, 0, -1, -1, 1], 9), ([1, 1, 0, 1, -2, -1, 1], 9), ([1, 1, 0, 1, 0, -2, 0], 18), ([1, 1, 0, 2, -2, -1, 0], 9), ([1, 1, 0, 2, -1, -1, -1], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 2, -1, 1, -1, -1, 0], 9), ([1, 2, 0, 0, -1, -1, 0], 9)]

theorem source399_checked : normalize (row ![1, 0, 1, -1, -1, 0] ![0, 0, 0, -1, 1, 0] (3, 3)) = source399 := by
  decide +kernel

theorem source399_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source399 (momentValues f) = 0 := by
  rw [← source399_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
