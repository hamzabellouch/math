import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source224 : Sparse := [([0, -1, 1, -1, 0, 2, -1], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 0, 0, 0, 0, 1, -1], -9), ([0, 0, 1, -2, 0, 2, -1], 9), ([0, 0, 1, -1, -1, 1, 0], -9), ([0, 0, 1, -1, -1, 2, -1], 9), ([0, 0, 1, -1, 0, 2, -2], -9), ([0, 0, 1, 0, 0, 1, -2], 9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 1, 1, -2, 0, 1, -1], -9), ([1, -1, 1, -1, 0, 1, 0], -9), ([1, -1, 1, -1, 0, 2, -1], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 0, 0, 0, 0, 1, -1], -9), ([1, 0, 1, -2, 0, 1, 0], -9), ([1, 0, 1, -2, 1, 1, -1], -9), ([1, 0, 1, -1, 0, 2, -2], -9), ([1, 0, 1, -1, 1, 1, -2], -9), ([1, 0, 1, 0, -1, 1, -1], -9), ([1, 0, 1, 0, 0, 1, -2], 9), ([1, 0, 2, -1, 0, 0, -1], -18), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 0, 1, -2], -9)]

theorem source224_checked : normalize (row ![0, 1, -1, 0, 1, -1] ![0, -1, 0, 0, 1, 0] (0, -3)) = source224 := by
  decide +kernel

theorem source224_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source224 (momentValues f) = 0 := by
  rw [← source224_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source225 : Sparse := [([0, -1, -1, 1, 0, -1, 2], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 2, 0, -1, 1], -9), ([0, -1, 0, 1, 0, -1, 1], 9), ([0, 0, -2, 1, 0, 0, 1], 18), ([0, 0, -1, 0, 1, -1, 1], 9), ([0, 0, -1, 1, -1, -1, 2], 9), ([0, 0, -1, 1, 1, -2, 1], 9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, -1, 2, -1, -1, 1], 9), ([0, 0, -1, 2, 0, -2, 1], 9), ([0, 0, -1, 2, 0, -1, 0], 9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, -1, 1, 0, -1, 0], 9), ([1, -1, -1, 1, 0, -1, 2], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, 0, -2, 1, 0, 0, 1], 18), ([1, 0, -1, 0, 0, -1, 2], -9), ([1, 0, -1, 0, 1, -1, 1], 9), ([1, 0, -1, 1, -1, -1, 2], 9), ([1, 0, -1, 1, 0, -2, 2], 9), ([1, 0, -1, 2, -1, -1, 1], 9), ([1, 0, -1, 2, 0, -1, 0], 9), ([1, 0, 0, 0, 0, -1, 1], 9), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, 0, -2, 1], 9), ([1, 1, -1, 1, 0, -1, 0], 9)]

theorem source225_checked : normalize (row ![0, -1, 1, 0, -1, 1] ![0, 1, 0, 0, -1, 0] (3, 3)) = source225 := by
  decide +kernel

theorem source225_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source225 (momentValues f) = 0 := by
  rw [← source225_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source226 : Sparse := [([0, -1, 1, 0, -1, 1, 0], 9), ([0, -1, 1, 0, -1, 2, -1], 9), ([0, -1, 1, 0, 0, 1, -1], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, 0, 0, 0, 0, 1, -1], 9), ([0, 0, 0, 1, -1, 1, -1], 9), ([0, 0, 1, -1, -1, 1, 0], 9), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 0, 1, 0, -1, 2, -2], 9), ([0, 0, 1, 0, 0, 1, -2], 9), ([0, 0, 1, 1, -2, 1, -1], 9), ([0, 0, 1, 1, -1, 1, -2], -9), ([0, 0, 2, 0, -1, 0, -1], 18), ([0, 1, 1, 0, -2, 1, -1], 9), ([0, 1, 1, 0, -1, 1, -2], 9), ([1, -1, 1, 0, -1, 1, 0], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 0, 1, -1, -1, 2, -1], 9), ([1, 0, 1, -1, 0, 1, -1], 9), ([1, 0, 1, 0, -2, 1, 0], -9), ([1, 0, 1, 0, -2, 2, -1], 9), ([1, 0, 1, 0, 0, 1, -2], 9), ([1, 0, 1, 1, -2, 1, -1], 9), ([1, 0, 2, 0, -1, 0, -1], 18), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, 0, -2, 1, -1], 9), ([1, 1, 1, 0, -1, 1, -2], 9)]

theorem source226_checked : normalize (row ![0, 1, 0, -1, 1, -1] ![0, -1, 0, 0, 1, 0] (3, 3)) = source226 := by
  decide +kernel

theorem source226_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source226 (momentValues f) = 0 := by
  rw [← source226_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source227 : Sparse := [([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, 0, -1, -1, 1, -1, 2], -9), ([0, 0, -1, 0, 1, -2, 2], 9), ([0, 0, -1, 0, 2, -2, 1], -9), ([0, 0, -1, 0, 2, -1, 0], 9), ([0, 0, -1, 1, 1, -2, 1], -9), ([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 0, 0, 0, -1, 1], 9), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 1, -1, 0, 0, -1, 1], -9), ([0, 1, -1, 0, 1, -2, 1], 9), ([1, -1, -1, 0, 1, -1, 2], -9), ([1, -1, -1, 0, 2, -1, 1], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, 0, -2, 0, 1, 0, 1], -18), ([1, 0, -1, -1, 2, -1, 1], -9), ([1, 0, -1, 0, 0, -1, 2], -9), ([1, 0, -1, 0, 2, -2, 1], -9), ([1, 0, -1, 0, 2, -1, 0], 9), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, -1, 1, 1, -2, 1], -9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, 0, 1, -1, 0], -9)]

theorem source227_checked : normalize (row ![0, -1, 0, 1, -1, 1] ![0, 1, 0, 0, -1, 0] (0, -3)) = source227 := by
  decide +kernel

theorem source227_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source227 (momentValues f) = 0 := by
  rw [← source227_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source228 : Sparse := [([0, -2, 1, -1, 0, 1, 1], 9), ([0, -2, 1, -1, 1, 0, 1], 9), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 1, -2, 0, 0, 2], 9), ([0, -1, 1, -2, 0, 1, 1], 9), ([0, -1, 1, -2, 1, 0, 1], -9), ([0, -1, 1, -1, 0, -1, 2], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, -1, 2, -1, 0, 0, 0], 18), ([0, 0, 0, -1, 0, 0, 1], 9), ([0, 0, 1, -2, 0, 0, 1], 9), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, -1, 0, -1, 1], -9), ([1, -2, 1, -1, 0, 0, 2], 9), ([1, -2, 1, -1, 0, 1, 1], 9), ([1, -2, 1, -1, 1, 0, 1], 9), ([1, -2, 1, 0, 0, 0, 1], -9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 0, 0, 0, 0, 1], 9), ([1, -1, 1, -2, 0, 1, 1], 9), ([1, -1, 1, -1, -1, 0, 2], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 2, -1, 0, 0, 0], 18), ([1, 0, 1, -2, 0, 0, 1], 9), ([1, 0, 1, -1, -1, 0, 1], 9)]

theorem source228_checked : normalize (row ![-1, 1, -1, 0, 0, 1] ![0, -1, 0, 0, 0, 1] (3, 3)) = source228 := by
  decide +kernel

theorem source228_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source228 (momentValues f) = 0 := by
  rw [← source228_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source229 : Sparse := [([0, 0, -1, 1, 0, 1, -1], -9), ([0, 0, 0, 1, 0, 0, -1], 9), ([0, 1, -1, 1, 0, 1, -2], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, -1, 1, 1, 0, -2], -9), ([0, 1, -1, 2, -1, 0, -1], -9), ([0, 1, -1, 2, 0, 0, -2], 9), ([0, 1, 0, 0, 0, 0, -1], -9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 2, -1, 0, 0, 0, -1], 9), ([0, 2, -1, 1, 0, 0, -2], -9), ([1, 0, -1, 1, 1, 0, -1], -9), ([1, 0, -1, 2, 0, 0, -1], -9), ([1, 1, -2, 1, 0, 0, 0], -18), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 1, 1, 0, -2], -9), ([1, 1, -1, 2, 0, -1, -1], -9), ([1, 1, 0, 0, 0, 0, -1], -9), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 2, -1, 0, 0, 0, -1], 9), ([1, 2, -1, 1, -1, 0, -1], -9), ([1, 2, -1, 1, 0, -1, -1], -9), ([1, 2, -1, 1, 0, 0, -2], -9)]

theorem source229_checked : normalize (row ![1, -1, 1, 0, 0, -1] ![0, 1, 0, 0, 0, -1] (0, -3)) = source229 := by
  decide +kernel

theorem source229_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source229 (momentValues f) = 0 := by
  rw [← source229_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source230 : Sparse := [([0, -2, 1, 0, -1, 0, 2], 9), ([0, -2, 1, 1, -1, 0, 1], -9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, -1, 0, 0, 0, 0, 1], -9), ([0, -1, 0, 1, -1, 0, 1], 9), ([0, -1, 1, -1, -1, 0, 2], -9), ([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 1, 0, -2, 0, 2], 9), ([0, -1, 1, 0, -2, 1, 1], -9), ([0, -1, 1, 0, -1, -1, 2], -9), ([0, 0, 0, 0, -1, 0, 1], -9), ([0, 0, 1, 0, -1, -1, 1], 9), ([1, -2, 1, 0, -1, 1, 1], -9), ([1, -2, 1, 0, 0, 0, 1], -9), ([1, -1, 0, 0, 0, 0, 1], -9), ([1, -1, 1, -1, -1, 0, 2], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 0, 0, 1], 9), ([1, -1, 1, 0, -1, -1, 2], -9), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 1, -2, 0, 1], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 2, 0, -1, 0, 0], -18), ([1, 0, 0, 0, -1, 0, 1], -9), ([1, 0, 1, -1, -1, 0, 1], -9), ([1, 0, 1, 0, -2, 0, 1], -9), ([1, 0, 1, 0, -1, -1, 1], 9)]

theorem source230_checked : normalize (row ![-1, 1, 0, -1, 0, 1] ![0, -1, 0, 0, 0, 1] (0, -3)) = source230 := by
  decide +kernel

theorem source230_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source230 (momentValues f) = 0 := by
  rw [← source230_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source231 : Sparse := [([0, 0, -1, 0, 2, 0, -1], 9), ([0, 0, -1, 1, 1, 0, -1], 9), ([0, 1, -2, 0, 1, 0, 0], 18), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, -1, 2, 0, -1], 9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, -1, 0, 2, -1, -1], -9), ([0, 1, -1, 0, 2, 0, -2], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 2, -1, -1, 1, 0, -1], -9), ([0, 2, -1, 0, 0, 0, -1], 9), ([0, 2, -1, 0, 1, -1, -1], 9), ([0, 2, -1, 0, 1, 0, -2], 9), ([1, 0, -1, 0, 1, 1, -1], -9), ([1, 0, -1, 0, 2, 0, -1], 9), ([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, 0, 0, 1, 0, -1], 9), ([1, 1, -2, 0, 1, 0, 0], 18), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, -1, 2, 0, -1], 9), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, -1, 0, 1, 1, -2], 9), ([1, 1, -1, 1, 0, 0, -1], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 1, 1, 0, -2], 9), ([1, 1, 0, 0, 0, 0, -1], 9), ([1, 2, -1, 0, 0, 0, -1], 9), ([1, 2, -1, 0, 1, -1, -1], 9)]

theorem source231_checked : normalize (row ![1, -1, 0, 1, 0, -1] ![0, 1, 0, 0, 0, -1] (3, 3)) = source231 := by
  decide +kernel

theorem source231_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source231 (momentValues f) = 0 := by
  rw [← source231_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
