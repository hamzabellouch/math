import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source352 : Sparse := [([0, -2, 0, 0, 1, -1, 2], 9), ([0, -2, 0, 0, 1, 0, 1], 9), ([0, -2, 0, 1, 1, -1, 1], 9), ([0, -2, 1, 0, 1, -1, 1], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 0, 0, 1, -2, 2], 9), ([0, -1, 0, 0, 2, -1, 0], 18), ([0, -1, 0, 1, 0, -1, 1], 9), ([0, -1, 0, 1, 1, -2, 1], -9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, -1, 1, 0, 1, -2, 1], 9), ([0, 0, -1, 0, 1, -1, 1], 9), ([0, 0, 0, 0, 1, -2, 1], 9), ([1, -2, 0, 0, 1, 0, 1], 9), ([1, -2, 0, 1, 1, -1, 1], 9), ([1, -1, -1, 0, 1, -1, 2], 9), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, 0, -1, 1, -1, 2], 9), ([1, -1, 0, -1, 1, 0, 1], 9), ([1, -1, 0, 0, 0, 0, 1], 9), ([1, -1, 0, 0, 2, -1, 0], 18), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, 1, -2, 1], 9), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, 0, -1, 1, -1, 1], -9), ([1, 0, 0, 0, 0, -1, 1], 9), ([1, 0, 0, 0, 1, -2, 1], 9)]

theorem source352_checked : normalize (row ![-1, 0, 0, 1, -1, 1] ![0, 0, 0, -1, 0, 1] (3, 3)) = source352 := by
  decide +kernel

theorem source352_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source352 (momentValues f) = 0 := by
  rw [← source352_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source353 : Sparse := [([0, 0, 0, 0, 0, 1, -1], -9), ([0, 0, 0, 1, -1, 1, -1], 9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, 0, -1, -1, 2, -1], -9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 1, 0, 0, -1, 2, -2], 9), ([0, 1, 0, 0, 0, 0, -1], -9), ([0, 1, 0, 1, -1, 1, -2], -9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 1, 1, 0, -1, 1, -2], -9), ([0, 2, -1, 0, -1, 1, -1], -9), ([0, 2, 0, 0, -1, 1, -2], 9), ([1, 0, 0, 0, -1, 2, -1], -9), ([1, 0, 0, 0, 0, 1, -1], -9), ([1, 0, 0, 1, -1, 1, -1], 9), ([1, 0, 1, 0, -1, 1, -1], -9), ([1, 1, -1, 0, -1, 2, -1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, 0, 0, -2, 1, 0], -18), ([1, 1, 0, 0, 0, 0, -1], -9), ([1, 1, 0, 1, -1, 0, -1], -9), ([1, 1, 0, 1, -1, 1, -2], -9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, 0, -1, 0, -1], 9), ([1, 1, 1, 0, -1, 1, -2], -9), ([1, 2, 0, -1, -1, 1, -1], -9), ([1, 2, 0, 0, -1, 0, -1], -9)]

theorem source353_checked : normalize (row ![1, 0, 0, -1, 1, -1] ![0, 0, 0, 1, 0, -1] (0, -3)) = source353 := by
  decide +kernel

theorem source353_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source353 (momentValues f) = 0 := by
  rw [← source353_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source354 : Sparse := [([0, -1, -1, -1, 1, 0, 2], -9), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, 0, -2, -1, 1, 0, 2], 9), ([0, 0, -2, -1, 1, 1, 1], -9), ([0, 0, -1, -2, 1, 0, 2], 9), ([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, -1, -1, 1, -1, 2], -9), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 1, -1, 1], 9), ([0, 0, 0, -1, 0, 0, 1], -9), ([0, 1, -1, -2, 1, 0, 1], -9), ([0, 1, -1, -1, 0, 0, 1], 9), ([1, -1, -1, -1, 1, 0, 2], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, 0, 1, 0, 1], -9), ([1, -1, 0, -1, 1, 0, 1], 9), ([1, 0, -2, 0, 1, 0, 1], -9), ([1, 0, -1, -2, 1, 1, 1], -9), ([1, 0, -1, -1, 1, -1, 2], -9), ([1, 0, -1, -1, 2, 0, 0], -18), ([1, 0, -1, 0, 0, 0, 1], -9), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, 0, -2, 1, 0, 1], -9), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 0, -1, 1, -1, 1], -9), ([1, 1, -2, -1, 1, 0, 1], -9), ([1, 1, -1, -1, 1, -1, 1], -9)]

theorem source354_checked : normalize (row ![0, -1, -1, 1, 0, 1] ![0, 0, 0, -1, 0, 1] (0, -3)) = source354 := by
  decide +kernel

theorem source354_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source354 (momentValues f) = 0 := by
  rw [← source354_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source355 : Sparse := [([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 1, 0, 0, -1], 9), ([0, -1, 1, 2, -1, 0, -1], -9), ([0, -1, 2, 1, -1, 0, -1], 9), ([0, 0, 0, 1, -1, 1, -1], 9), ([0, 0, 0, 2, -1, 0, -1], 9), ([0, 0, 1, 1, -2, 0, 0], 18), ([0, 0, 1, 1, 0, -1, -1], 9), ([0, 0, 1, 2, -1, -1, -1], 9), ([0, 0, 1, 2, -1, 0, -2], 9), ([0, 0, 2, 0, -1, 0, -1], 9), ([0, 0, 2, 1, -1, -1, -1], -9), ([0, 0, 2, 1, -1, 0, -2], 9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 2, 1, -1, 0, -1], 9), ([1, 0, 0, 1, -1, 1, -1], 9), ([1, 0, 0, 1, 0, 0, -1], 9), ([1, 0, 0, 2, -1, 0, -1], 9), ([1, 0, 1, 0, -1, 1, -1], -9), ([1, 0, 1, 0, 0, 0, -1], 9), ([1, 0, 1, 1, -2, 0, 0], 18), ([1, 0, 1, 1, -1, 1, -2], 9), ([1, 0, 1, 2, -1, -1, -1], 9), ([1, 0, 2, 0, -1, 0, -1], 9), ([1, 1, 0, 1, -1, 0, -1], -9), ([1, 1, 1, 0, -1, 0, -1], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, -1, 0, -2], 9)]

theorem source355_checked : normalize (row ![0, 1, 1, -1, 0, -1] ![0, 0, 0, 1, 0, -1] (3, 3)) = source355 := by
  decide +kernel

theorem source355_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source355 (momentValues f) = 0 := by
  rw [← source355_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source356 : Sparse := [([0, -1, -1, 0, 1, -1, 2], 9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, 0, -2, 1, 1, -1, 1], 9), ([0, 0, -1, -1, 1, 0, 1], 9), ([0, 0, -1, 0, 1, -2, 2], 9), ([0, 0, -1, 0, 2, -1, 0], 18), ([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, -1, 1, 1, -2, 1], -9), ([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 0, 0, 0, -1, 1], 9), ([0, 0, 0, 0, 1, -2, 1], 9), ([0, 1, -2, 0, 1, -1, 1], 9), ([0, 1, -1, 0, 1, -2, 1], 9), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, 0, -2, 0, 1, -1, 2], 9), ([1, 0, -2, 0, 1, 0, 1], -9), ([1, 0, -2, 1, 1, -1, 1], 9), ([1, 0, -1, -1, 1, -1, 2], 9), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 0, -1, 0, 2, -1, 0], 18), ([1, 0, 0, -1, 1, -1, 1], 9), ([1, 0, 0, 0, 1, -2, 1], 9), ([1, 1, -2, 0, 1, -1, 1], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, -1, 0, 1, -2, 1], 9)]

theorem source356_checked : normalize (row ![0, -1, 0, 1, -1, 1] ![0, 0, 0, -1, 0, 1] (3, 3)) = source356 := by
  decide +kernel

theorem source356_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source356 (momentValues f) = 0 := by
  rw [← source356_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source357 : Sparse := [([0, -1, 1, 0, 0, 1, -1], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, 0, 0, 0, 0, 1, -1], 9), ([0, 0, 1, -1, -1, 2, -1], -9), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 0, 1, 0, -1, 2, -2], 9), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 0, 1, 1, -1, 1, -2], -9), ([0, 0, 2, 0, -1, 0, -1], 9), ([0, 0, 2, 0, -1, 1, -2], -9), ([0, 1, 0, 0, -1, 1, -1], -9), ([0, 1, 1, 0, -1, 1, -2], 9), ([1, -1, 1, 0, -1, 2, -1], -9), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 2, 0, -1, 1, -1], -9), ([1, 0, 0, 0, -1, 2, -1], -9), ([1, 0, 0, 1, -1, 1, -1], -9), ([1, 0, 1, 0, -2, 1, 0], -18), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 0, 1, 1, -1, 0, -1], -9), ([1, 0, 1, 1, -1, 1, -2], -9), ([1, 0, 2, -1, -1, 1, -1], -9), ([1, 0, 2, 0, -1, 0, -1], 9), ([1, 0, 2, 0, -1, 1, -2], -9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, 0, -1, 0, -1], -9)]

theorem source357_checked : normalize (row ![0, 1, 0, -1, 1, -1] ![0, 0, 0, 1, 0, -1] (0, -3)) = source357 := by
  decide +kernel

theorem source357_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source357 (momentValues f) = 0 := by
  rw [← source357_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source358 : Sparse := [([0, -1, 0, -1, 1, -1, 2], -9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, 0, -1, -1, 1, -1, 2], 9), ([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, 0, -2, 1, -1, 2], 9), ([0, 0, 0, -1, 0, 0, 1], 9), ([0, 0, 0, -1, 1, -2, 2], -9), ([0, 0, 0, 0, 0, -1, 1], -9), ([0, 0, 0, 0, 1, -2, 1], 9), ([0, 0, 1, -1, 0, -1, 1], -9), ([0, 1, 0, -2, 1, -1, 1], -9), ([0, 1, 0, -1, 0, -1, 1], 9), ([1, -1, 0, -1, 1, -1, 2], -9), ([1, -1, 0, -1, 1, 0, 1], -9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, 0, -1, 0, 1, -1, 1], -9), ([1, 0, 0, -2, 1, 0, 1], -9), ([1, 0, 0, -1, 1, -2, 2], -9), ([1, 0, 0, -1, 2, -1, 0], -18), ([1, 0, 0, 0, 0, -1, 1], -9), ([1, 0, 0, 0, 1, -2, 1], 9), ([1, 0, 1, -2, 1, -1, 1], -9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 0, 1, -1, 1, -2, 1], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, 0, -1, 1, -2, 1], -9)]

theorem source358_checked : normalize (row ![0, 0, -1, 1, -1, 1] ![0, 0, 0, -1, 0, 1] (0, -3)) = source358 := by
  decide +kernel

theorem source358_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source358 (momentValues f) = 0 := by
  rw [← source358_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source359 : Sparse := [([0, -1, 0, 1, -1, 2, -1], 9), ([0, -1, 0, 1, 0, 1, -1], 9), ([0, -1, 0, 2, -1, 1, -1], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, 0, -1, 1, -1, 2, -1], 9), ([0, 0, -1, 2, -1, 1, -1], 9), ([0, 0, 0, 1, -2, 1, 0], 18), ([0, 0, 0, 1, 0, 0, -1], 9), ([0, 0, 0, 2, -1, 0, -1], 9), ([0, 0, 0, 2, -1, 1, -2], 9), ([0, 0, 1, 0, -1, 1, -1], 9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 0, 1, 1, -1, 1, -2], 9), ([0, 1, 0, 0, -1, 1, -1], 9), ([0, 1, 0, 1, -1, 0, -1], 9), ([1, -1, 0, 1, -1, 2, -1], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, 0, -1, 1, -1, 2, -1], 9), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 0, -1, 2, -1, 1, -1], 9), ([1, 0, 0, 0, -1, 2, -1], -9), ([1, 0, 0, 0, 0, 1, -1], 9), ([1, 0, 0, 1, -2, 1, 0], 18), ([1, 0, 0, 1, -1, 2, -2], 9), ([1, 0, 0, 2, -1, 0, -1], 9), ([1, 0, 1, 0, -1, 1, -1], 9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 1, 0, 1, -1, 0, -1], 9), ([1, 1, 0, 1, -1, 1, -2], 9)]

theorem source359_checked : normalize (row ![0, 0, 1, -1, 1, -1] ![0, 0, 0, 1, 0, -1] (3, 3)) = source359 := by
  decide +kernel

theorem source359_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source359 (momentValues f) = 0 := by
  rw [← source359_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
