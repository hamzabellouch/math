import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source408 : Sparse := [([0, -2, -1, 0, 0, 1, 2], 9), ([0, -2, -1, 0, 1, 1, 1], -9), ([0, -1, -2, 0, 0, 1, 2], -9), ([0, -1, -1, -1, 0, 1, 2], 9), ([0, -1, -1, 0, -1, 1, 2], -9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, 0, -1, 0, 1, 1], -9), ([0, -1, 0, 0, 0, 0, 1], 9), ([0, 0, -2, 0, 0, 1, 1], 9), ([0, 0, -1, 0, 0, 0, 1], -9), ([1, -2, -1, 1, 0, 1, 1], -9), ([1, -2, 0, 0, 0, 1, 1], -9), ([1, -1, -2, 0, 0, 1, 2], -9), ([1, -1, -2, 0, 1, 1, 1], -9), ([1, -1, -2, 1, 0, 1, 1], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, 0, -1, 1, 2], -9), ([1, -1, -1, 0, 0, 2, 0], -18), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, 0, -2, 0, 0, 1, 1], 9), ([1, 0, -1, -1, 0, 1, 1], -9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, -1, 0, 0, 0, 1], -9)]

theorem source408_checked : normalize (row ![-1, -1, 0, 0, 1, 1] ![0, 0, 0, 0, -1, 1] (0, -3)) = source408 := by
  decide +kernel

theorem source408_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source408 (momentValues f) = 0 := by
  rw [← source408_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source409 : Sparse := [([0, 0, 1, 0, 1, -1, -1], 9), ([0, 0, 1, 1, 0, -1, -1], 9), ([0, 1, 0, 0, 0, 0, -1], 9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 1, 1, 0, 0, -2, 0], 18), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, 0, -1, -2], 9), ([0, 1, 2, -1, 0, -1, -1], 9), ([0, 1, 2, 0, -1, -1, -1], 9), ([0, 2, 0, 0, 0, -1, -1], 9), ([0, 2, 1, -1, 0, -1, -1], 9), ([0, 2, 1, 0, -1, -1, -1], -9), ([0, 2, 1, 0, 0, -1, -2], 9), ([1, 0, 1, 0, 0, 0, -1], 9), ([1, 0, 1, 0, 1, -1, -1], 9), ([1, 0, 1, 1, 0, -1, -1], 9), ([1, 0, 2, 0, 0, -1, -1], -9), ([1, 1, 0, 0, 1, -1, -1], 9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, 0, -2, 0], 18), ([1, 1, 1, 0, 1, -1, -2], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 2, -1, 0, -1, -1], 9), ([1, 1, 2, 0, -1, -1, -1], 9), ([1, 1, 2, 0, 0, -1, -2], 9), ([1, 2, 0, 0, 0, -1, -1], 9), ([1, 2, 1, -1, 0, -1, -1], 9)]

theorem source409_checked : normalize (row ![1, 1, 0, 0, -1, -1] ![0, 0, 0, 0, 1, -1] (3, 3)) = source409 := by
  decide +kernel

theorem source409_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source409 (momentValues f) = 0 := by
  rw [← source409_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source410 : Sparse := [([0, -2, 0, -1, 0, 1, 2], 9), ([0, -2, 0, -1, 1, 1, 1], -9), ([0, -1, -1, -1, 0, 1, 2], -9), ([0, -1, 0, -2, 0, 1, 2], 9), ([0, -1, 0, -1, -1, 1, 2], -9), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, -1, 0, 0, 0, 0, 1], -9), ([0, -1, 1, -2, 0, 1, 1], -9), ([0, -1, 1, -1, 0, 0, 1], 9), ([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, 0, -1, 0, 0, 1], -9), ([1, -2, 0, 0, 0, 1, 1], -9), ([1, -2, 1, -1, 0, 1, 1], -9), ([1, -1, -1, -1, 0, 1, 2], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, 0, 0, 1, 1], -9), ([1, -1, 0, -2, 1, 1, 1], -9), ([1, -1, 0, -1, -1, 1, 2], -9), ([1, -1, 0, -1, 0, 2, 0], -18), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, -1, 0, 0, 0, 0, 1], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, 0, -1, -1, 0, 1, 1], 9), ([1, 0, 0, -2, 0, 1, 1], -9), ([1, 0, 0, -1, -1, 1, 1], -9), ([1, 0, 0, -1, 0, 0, 1], -9)]

theorem source410_checked : normalize (row ![-1, 0, -1, 0, 1, 1] ![0, 0, 0, 0, -1, 1] (0, -3)) = source410 := by
  decide +kernel

theorem source410_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source410 (momentValues f) = 0 := by
  rw [← source410_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source411 : Sparse := [([0, 0, 0, 1, 1, -1, -1], 9), ([0, 0, 0, 2, 0, -1, -1], 9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, -1, 2, 0, -1, -1], -9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 1, 0, 1, 0, -2, 0], 18), ([0, 1, 0, 2, -1, -1, -1], 9), ([0, 1, 0, 2, 0, -1, -2], 9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 2, -1, 1, 0, -1, -1], 9), ([0, 2, 0, 0, 0, -1, -1], 9), ([0, 2, 0, 1, -1, -1, -1], -9), ([0, 2, 0, 1, 0, -1, -2], 9), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 0, 0, 1, 1, -1, -1], 9), ([1, 0, 0, 2, 0, -1, -1], 9), ([1, 0, 1, 1, 0, -1, -1], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, 0, 0, 0, -1], 9), ([1, 1, 0, 0, 1, -1, -1], -9), ([1, 1, 0, 1, 0, -2, 0], 18), ([1, 1, 0, 1, 1, -1, -2], 9), ([1, 1, 0, 2, -1, -1, -1], 9), ([1, 1, 1, 0, 0, -1, -1], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, 0, -1, -2], 9), ([1, 2, -1, 1, 0, -1, -1], 9), ([1, 2, 0, 0, 0, -1, -1], 9)]

theorem source411_checked : normalize (row ![1, 0, 1, 0, -1, -1] ![0, 0, 0, 0, 1, -1] (3, 3)) = source411 := by
  decide +kernel

theorem source411_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source411 (momentValues f) = 0 := by
  rw [← source411_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source412 : Sparse := [([0, -2, 0, 1, -1, 1, 1], 9), ([0, -2, 1, 0, -1, 1, 1], 9), ([0, -1, -1, 0, -1, 1, 2], 9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, 0, -1, 0, 1, 1], 9), ([0, -1, 0, 0, -2, 1, 2], 9), ([0, -1, 0, 0, -1, 2, 0], 18), ([0, -1, 0, 1, -2, 1, 1], -9), ([0, -1, 0, 1, -1, 0, 1], 9), ([0, -1, 1, 0, -2, 1, 1], 9), ([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 0, 0, -2, 1, 1], 9), ([0, 0, 0, 0, -1, 0, 1], 9), ([1, -2, 0, 0, -1, 1, 2], 9), ([1, -2, 0, 0, 0, 1, 1], -9), ([1, -2, 0, 1, -1, 1, 1], 9), ([1, -2, 1, 0, -1, 1, 1], 9), ([1, -1, -1, 0, 0, 1, 1], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, 0, -1, -1, 1, 2], 9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 0, 0, -1, 2, 0], 18), ([1, -1, 0, 0, 0, 0, 1], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, 0, -2, 1, 1], 9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, 0, 0, -1, -1, 1, 1], 9), ([1, 0, 0, 0, -2, 1, 1], 9)]

theorem source412_checked : normalize (row ![-1, 0, 0, -1, 1, 1] ![0, 0, 0, 0, -1, 1] (3, 3)) = source412 := by
  decide +kernel

theorem source412_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source412 (momentValues f) = 0 := by
  rw [← source412_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source413 : Sparse := [([0, 0, 0, 0, 1, 0, -1], 9), ([0, 0, 1, 0, 1, -1, -1], -9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 1, 0, -1, 2, -1, -1], -9), ([0, 1, 0, 0, 0, 0, -1], -9), ([0, 1, 0, 0, 2, -1, -2], 9), ([0, 1, 0, 1, 1, -1, -2], -9), ([0, 1, 1, 0, 1, -1, -2], 9), ([0, 2, 0, 0, 0, -1, -1], 9), ([0, 2, 0, 0, 1, -1, -2], -9), ([1, 0, 0, 0, 2, -1, -1], -9), ([1, 0, 0, 1, 1, -1, -1], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, -1, 0, 2, -1, -1], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, 0, 0, 0, -1], -9), ([1, 1, 0, 0, 1, -2, 0], -18), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 1, 0, 1, 1, -1, -2], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, 0, -1, -1], -9), ([1, 2, -1, 0, 1, -1, -1], -9), ([1, 2, 0, -1, 1, -1, -1], -9), ([1, 2, 0, 0, 0, -1, -1], 9), ([1, 2, 0, 0, 1, -1, -2], -9)]

theorem source413_checked : normalize (row ![1, 0, 0, 1, -1, -1] ![0, 0, 0, 0, 1, -1] (0, -3)) = source413 := by
  decide +kernel

theorem source413_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source413 (momentValues f) = 0 := by
  rw [← source413_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source414 : Sparse := [([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, 0, -1, 0, 1, 1], 9), ([0, 0, -2, -1, 0, 1, 2], 9), ([0, 0, -2, -1, 1, 1, 1], 9), ([0, 0, -2, 0, 0, 1, 1], 9), ([0, 0, -1, -2, 1, 1, 1], 9), ([0, 0, -1, -1, -1, 1, 2], 9), ([0, 0, -1, -1, 0, 2, 0], 18), ([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, 0, -1, -1, 1, 1], 9), ([0, 1, -2, -1, 0, 1, 1], -9), ([0, 1, -1, -2, 0, 1, 1], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 0, 0, 1], 9), ([1, -1, -1, -1, 0, 1, 2], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, 0, 0, 1, 1], 9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, 0, -2, -1, 1, 1, 1], 9), ([1, 0, -2, 0, 0, 1, 1], 9), ([1, 0, -1, -2, 0, 1, 2], 9), ([1, 0, -1, -2, 1, 1, 1], 9), ([1, 0, -1, -1, 0, 2, 0], 18), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, 0, -2, 0, 1, 1], -9), ([1, 0, 0, -1, -1, 1, 1], 9), ([1, 0, 0, -1, 0, 0, 1], 9), ([1, 1, -1, -2, 0, 1, 1], 9), ([1, 1, -1, -1, -1, 1, 1], 9)]

theorem source414_checked : normalize (row ![0, -1, -1, 0, 1, 1] ![0, 0, 0, 0, -1, 1] (3, 3)) = source414 := by
  decide +kernel

theorem source414_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source414 (momentValues f) = 0 := by
  rw [← source414_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source415 : Sparse := [([0, -1, 1, 1, 0, 0, -1], 9), ([0, -1, 2, 1, 0, -1, -1], -9), ([0, 0, 0, 1, 0, 0, -1], -9), ([0, 0, 0, 2, 0, -1, -1], 9), ([0, 0, 1, 0, 0, 0, -1], 9), ([0, 0, 1, 0, 1, -1, -1], -9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 0, 1, 1, 1, -1, -2], 9), ([0, 0, 1, 2, 0, -1, -2], -9), ([0, 0, 2, 1, 0, -1, -2], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, 0, -1, -2], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 1, 2, 0, -1, -1], -9), ([1, 0, 0, 1, 0, 0, -1], -9), ([1, 0, 0, 1, 1, -1, -1], -9), ([1, 0, 0, 2, 0, -1, -1], 9), ([1, 0, 1, 1, -1, 0, -1], -9), ([1, 0, 1, 1, 0, -2, 0], -18), ([1, 0, 1, 2, -1, -1, -1], -9), ([1, 0, 1, 2, 0, -1, -2], -9), ([1, 0, 2, 0, 0, -1, -1], -9), ([1, 0, 2, 1, -1, -1, -1], -9), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 1, 1, 0, 0, -1, -1], -9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, 0, -1, -2], -9)]

theorem source415_checked : normalize (row ![0, 1, 1, 0, -1, -1] ![0, 0, 0, 0, 1, -1] (0, -3)) = source415 := by
  decide +kernel

theorem source415_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source415 (momentValues f) = 0 := by
  rw [← source415_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
