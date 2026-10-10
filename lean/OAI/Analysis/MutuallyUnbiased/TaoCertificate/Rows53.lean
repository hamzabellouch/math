import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source424 : Sparse := [([0, 1, -2, 0, 1, -1, 1], -9), ([0, 1, -1, 0, -1, 0, 1], 9), ([0, 1, -1, 0, 0, 0, 0], -9), ([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, -1, 1, 0, -2, 1], -9), ([0, 1, -1, 1, 0, -1, 0], 9), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 1, 0, 0, 0, -1, 0], -9), ([0, 2, -2, 0, 0, -1, 1], 9), ([0, 2, -1, -1, 0, -1, 1], -9), ([0, 2, -1, 0, -1, -1, 1], -9), ([0, 2, -1, 0, 0, -2, 1], 9), ([1, 0, -1, 0, 0, -1, 2], -18), ([1, 1, -2, 0, 0, 0, 1], -9), ([1, 1, -2, 1, 0, -1, 1], -9), ([1, 1, -1, -1, 0, 0, 1], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 0, 0, 0, 0], -9), ([1, 1, -1, 0, 1, -2, 1], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, 0, -1, 0, -1, 1], 9), ([1, 1, 0, 0, -1, -1, 1], -9), ([1, 1, 0, 0, 0, -2, 1], -9), ([1, 1, 0, 0, 0, -1, 0], -9), ([1, 2, -1, -1, 0, -1, 1], -9), ([1, 2, -1, 0, -1, -1, 1], -9)]

theorem source424_checked : normalize (row ![1, -1, 0, 0, -1, 1] ![1, 0, 0, 0, 0, -1] (0, -3)) = source424 := by
  decide +kernel

theorem source424_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source424 (momentValues f) = 0 := by
  rw [← source424_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source425 : Sparse := [([0, -2, 1, 0, 0, 2, -1], 9), ([0, -2, 2, 0, 0, 1, -1], 9), ([0, -1, 0, 0, 0, 2, -1], 9), ([0, -1, 0, 0, 1, 1, -1], 9), ([0, -1, 1, -1, 0, 1, 0], 9), ([0, -1, 1, -1, 0, 2, -1], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, -1, 1, 0], 9), ([0, -1, 1, 0, -1, 2, -1], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 1, 0, 0, -1], 9), ([0, -1, 2, -1, 0, 1, -1], 9), ([0, -1, 2, 0, -1, 1, -1], -9), ([0, -1, 2, 0, 0, 0, -1], 9), ([0, 0, 1, 0, 0, 1, -2], 18), ([1, -2, 1, 0, 1, 1, -1], 9), ([1, -2, 1, 1, 0, 1, -1], 9), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, -1, 0, 0, 0, 2, -1], 9), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, -1, 2, -1], 9), ([1, -1, 1, 0, 0, 0, 0], 9), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 2, -1, 0, 1, -1], 9), ([1, -1, 2, 0, 0, 0, -1], 9), ([1, 0, 1, 0, 0, 1, -2], 18)]

theorem source425_checked : normalize (row ![-1, 1, 0, 0, 1, -1] ![-1, 0, 0, 0, 0, 1] (3, 3)) = source425 := by
  decide +kernel

theorem source425_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source425 (momentValues f) = 0 := by
  rw [← source425_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source426 : Sparse := [([0, 0, 0, -1, -1, 0, 2], 18), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, 0, -1, 0, 1], 9), ([0, 1, 0, -2, -1, 1, 1], 9), ([0, 1, 0, -2, 0, 0, 1], 9), ([0, 1, 0, -1, -2, 1, 1], -9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 1, 0, 0, -2, 0, 1], 9), ([0, 1, 1, -2, -1, 0, 1], -9), ([0, 1, 1, -1, -2, 0, 1], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, -1, 0, 0], 9), ([0, 2, 0, -2, -1, 0, 1], 9), ([0, 2, 0, -1, -2, 0, 1], 9), ([1, 0, 0, -1, -1, 0, 2], 18), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, 0, 0, 1], -9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, 0, -2, -1, 1, 1], 9), ([1, 1, 0, -2, 0, 0, 1], 9), ([1, 1, 0, -1, 0, -1, 1], 9), ([1, 1, 0, -1, 0, 0, 0], 9), ([1, 1, 0, 0, -2, 0, 1], 9), ([1, 1, 0, 0, -1, -1, 1], -9), ([1, 1, 0, 0, -1, 0, 0], 9), ([1, 1, 1, -1, -2, 0, 1], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 2, -1, -1, -1, 0, 1], 9), ([1, 2, 0, -1, -1, -1, 1], 9)]

theorem source426_checked : normalize (row ![1, 0, -1, -1, 0, 1] ![1, 0, 0, 0, 0, -1] (3, 3)) = source426 := by
  decide +kernel

theorem source426_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source426 (momentValues f) = 0 := by
  rw [← source426_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source427 : Sparse := [([0, -2, 0, 1, 1, 1, -1], -9), ([0, -2, 0, 1, 2, 0, -1], 9), ([0, -2, 0, 2, 1, 0, -1], 9), ([0, -2, 1, 1, 1, 0, -1], -9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, -1, -1, 2, 1, 0, -1], -9), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 1, 1, -1], 9), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, -1, 0, 1, 2, -1, -1], -9), ([0, -1, 1, 1, 0, 0, -1], 9), ([1, -2, 0, 1, 1, 1, -1], -9), ([1, -2, 1, 1, 1, 0, -1], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 1, 2, 0, -1], -9), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 0, 0, 2, 0, -1], -9), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, -1, 0, 2, 0, 0, -1], -9), ([1, -1, 0, 2, 1, -1, -1], -9), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, 0, 0, 1, 1, 0, -2], -18)]

theorem source427_checked : normalize (row ![-1, 0, 1, 1, 0, -1] ![-1, 0, 0, 0, 0, 1] (0, -3)) = source427 := by
  decide +kernel

theorem source427_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source427 (momentValues f) = 0 := by
  rw [← source427_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source428 : Sparse := [([0, 0, 0, -1, 0, -1, 2], 18), ([0, 1, -1, -1, 0, 0, 1], 9), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, 0, -2, 0, 0, 1], 9), ([0, 1, 0, -2, 1, -1, 1], 9), ([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 0, -1, 0, 0, 0], 9), ([0, 1, 0, -1, 1, -2, 1], 9), ([0, 1, 0, 0, -1, -1, 1], 9), ([0, 1, 1, -2, 0, -1, 1], -9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, 0, -2, 1], 9), ([0, 1, 1, -1, 0, -1, 0], 9), ([0, 2, 0, -2, 0, -1, 1], 9), ([0, 2, 0, -1, -1, -1, 1], 9), ([1, 0, 0, -1, 0, -1, 2], 18), ([1, 1, -1, -1, 0, 0, 1], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, 0, -2, 0, 0, 1], 9), ([1, 1, 0, -2, 1, -1, 1], 9), ([1, 1, 0, -1, 1, -2, 1], 9), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 1, 0, 0, -1, -1, 1], 9), ([1, 1, 0, 0, 0, -2, 1], -9), ([1, 1, 0, 0, 0, -1, 0], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, 0, -2, 1], 9), ([1, 2, -1, -1, 0, -1, 1], 9), ([1, 2, 0, -1, 0, -2, 1], 9)]

theorem source428_checked : normalize (row ![1, 0, -1, 0, -1, 1] ![1, 0, 0, 0, 0, -1] (3, 3)) = source428 := by
  decide +kernel

theorem source428_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source428 (momentValues f) = 0 := by
  rw [← source428_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source429 : Sparse := [([0, -2, 0, 1, 0, 2, -1], -9), ([0, -2, 0, 1, 1, 1, -1], 9), ([0, -2, 0, 2, 0, 1, -1], 9), ([0, -2, 1, 1, 0, 1, -1], -9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, -1, 2, 0, 1, -1], -9), ([0, -1, 0, 0, 0, 1, 0], -9), ([0, -1, 0, 0, 0, 2, -1], 9), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 1, 1, 0, -1], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([1, -2, 0, 1, 0, 2, -1], -9), ([1, -2, 1, 1, 0, 1, -1], -9), ([1, -1, -1, 1, 0, 2, -1], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, 0, 0, 0, 1, 0], -9), ([1, -1, 0, 0, 0, 2, -1], 9), ([1, -1, 0, 0, 1, 1, -1], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 0, 1, -1, 2, -1], -9), ([1, -1, 0, 2, -1, 1, -1], -9), ([1, -1, 0, 2, 0, 0, -1], -9), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, 0, 0, 1, 0, 1, -2], -18)]

theorem source429_checked : normalize (row ![-1, 0, 1, 0, 1, -1] ![-1, 0, 0, 0, 0, 1] (0, -3)) = source429 := by
  decide +kernel

theorem source429_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source429 (momentValues f) = 0 := by
  rw [← source429_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source430 : Sparse := [([0, 1, -1, 0, 0, -1, 1], -9), ([0, 1, 0, 0, -2, 0, 1], 9), ([0, 1, 0, 0, -1, 0, 0], -9), ([0, 1, 0, 0, 0, -1, 0], 9), ([0, 1, 0, 1, -1, -2, 1], -9), ([0, 1, 0, 1, -1, -1, 0], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 2, -1, 0, -1, -1, 1], 9), ([0, 2, 0, -1, -1, -1, 1], -9), ([0, 2, 0, 0, -2, -1, 1], -9), ([0, 2, 0, 0, -1, -2, 1], 9), ([1, 0, 0, 0, -1, -1, 2], -18), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, 0, -1, -1, 0, 1], -9), ([1, 1, 0, -1, 0, -1, 1], -9), ([1, 1, 0, 0, -2, 0, 1], 9), ([1, 1, 0, 0, -1, 0, 0], -9), ([1, 1, 0, 0, 0, -2, 1], -9), ([1, 1, 0, 1, -2, -1, 1], -9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, 0, -2, -1, 1], -9), ([1, 1, 1, 0, -1, -2, 1], -9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 2, 0, -1, -1, -1, 1], -9), ([1, 2, 0, 0, -2, -1, 1], -9)]

theorem source430_checked : normalize (row ![1, 0, 0, -1, -1, 1] ![1, 0, 0, 0, 0, -1] (0, -3)) = source430 := by
  decide +kernel

theorem source430_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source430 (momentValues f) = 0 := by
  rw [← source430_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source431 : Sparse := [([0, -2, 0, 0, 1, 2, -1], 9), ([0, -2, 1, 0, 1, 1, -1], 9), ([0, -1, -1, 0, 1, 2, -1], 9), ([0, -1, -1, 0, 2, 1, -1], 9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, -1, 0, -1, 1, 2, -1], -9), ([0, -1, 0, -1, 2, 1, -1], 9), ([0, -1, 0, 0, 0, 1, 0], 9), ([0, -1, 0, 0, 0, 2, -1], 9), ([0, -1, 0, 1, 0, 1, -1], 9), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, 0, 1, -1], -9), ([0, -1, 1, 0, 1, 0, -1], 9), ([0, 0, 0, 0, 1, 1, -2], 18), ([1, -2, 0, 0, 2, 1, -1], 9), ([1, -2, 0, 1, 1, 1, -1], 9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, -1, 0, 1, 2, -1], 9), ([1, -1, -1, 0, 2, 1, -1], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, 0, -1, 2, 1, -1], 9), ([1, -1, 0, 0, 0, 2, -1], 9), ([1, -1, 0, 0, 1, 0, 0], 9), ([1, -1, 0, 0, 2, 0, -1], -9), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, 0, 0, 0, 1, 1, -2], 18)]

theorem source431_checked : normalize (row ![-1, 0, 0, 1, 1, -1] ![-1, 0, 0, 0, 0, 1] (3, 3)) = source431 := by
  decide +kernel

theorem source431_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source431 (momentValues f) = 0 := by
  rw [← source431_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
