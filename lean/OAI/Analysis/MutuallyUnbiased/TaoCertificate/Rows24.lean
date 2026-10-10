import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source192 : Sparse := [([0, -2, 1, 1, -1, 0, 1], -9), ([0, -2, 1, 2, -1, 0, 0], 9), ([0, -1, 0, 1, -1, 0, 1], 9), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 1, 2, -2, 0, 0], -9), ([0, -1, 1, 2, -1, -1, 0], 9), ([0, -1, 1, 2, -1, 0, -1], -9), ([0, 0, 0, 1, -1, 0, 0], -9), ([0, 0, 1, 1, -2, 0, 0], 9), ([1, -2, 1, 1, -1, 1, 0], -9), ([1, -2, 1, 1, 0, 0, 0], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 1, 1, -2, 0, 1], -9), ([1, -1, 1, 1, -2, 1, 0], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 1, 2, -2, 0, 0], -9), ([1, -1, 1, 2, -1, 0, -1], -9), ([1, -1, 2, 0, -1, 0, 0], -18), ([1, 0, 0, 1, -1, 0, 0], -9), ([1, 0, 1, 1, -2, 0, 0], 9), ([1, 0, 1, 1, -1, -1, 0], -9), ([1, 0, 1, 1, -1, 0, -1], -9)]

theorem source192_checked : normalize (row ![-1, 1, 1, -1, 0, 0] ![0, -1, 1, 0, 0, 0] (0, -3)) = source192 := by
  decide +kernel

theorem source192_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source192 (momentValues f) = 0 := by
  rw [← source192_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source193 : Sparse := [([0, 0, -1, -1, 1, 0, 1], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 1, -2, 0, 1, 0, 0], 18), ([0, 1, -1, -2, 1, 1, 0], 9), ([0, 1, -1, -1, 0, 0, 1], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, -1, 2, -1, 0], 9), ([0, 1, -1, -1, 2, 0, -1], 9), ([0, 1, 0, -1, 0, 0, 0], 9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 2, -1, -2, 1, 0, 0], 9), ([0, 2, -1, -1, 0, 0, 0], 9), ([0, 2, -1, -1, 1, -1, 0], 9), ([0, 2, -1, -1, 1, 0, -1], -9), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, -1, -1, 1, 1, 0], 9), ([1, 0, -1, -1, 2, 0, 0], -9), ([1, 0, 0, -1, 1, 0, 0], 9), ([1, 1, -2, 0, 1, 0, 0], 18), ([1, 1, -1, -2, 1, 0, 1], 9), ([1, 1, -1, -2, 2, 0, 0], 9), ([1, 1, -1, -1, 0, 0, 1], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, -1, 2, -1, 0], 9), ([1, 1, -1, -1, 2, 0, -1], 9), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 2, -1, -1, 0, 0, 0], 9), ([1, 2, -1, -1, 1, -1, 0], 9)]

theorem source193_checked : normalize (row ![1, -1, -1, 1, 0, 0] ![0, 1, -1, 0, 0, 0] (3, 3)) = source193 := by
  decide +kernel

theorem source193_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source193 (momentValues f) = 0 := by
  rw [← source193_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source194 : Sparse := [([0, -2, 1, 1, 0, -1, 1], -9), ([0, -2, 1, 2, 0, -1, 0], 9), ([0, -1, 0, 1, 0, -1, 1], 9), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, -1, 1, 1, 0, 0, -1], 9), ([0, -1, 1, 1, 1, -2, 0], -9), ([0, -1, 1, 2, -1, -1, 0], -9), ([0, -1, 1, 2, 0, -2, 0], 9), ([0, -1, 1, 2, 0, -1, -1], -9), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 0, 1, 1, -1, -1, 0], 9), ([1, -2, 1, 1, 0, 0, 0], -9), ([1, -2, 1, 1, 1, -1, 0], -9), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 1, 1, 0, -2, 1], -9), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 1, 2, -1, -1, 0], -9), ([1, -1, 1, 2, 0, -1, -1], -9), ([1, -1, 2, 0, 0, -1, 0], -18), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 0, 1, 1, -1, -1, 0], 9), ([1, 0, 1, 1, 0, -2, 0], -9), ([1, 0, 1, 1, 0, -1, -1], -9)]

theorem source194_checked : normalize (row ![-1, 1, 1, 0, -1, 0] ![0, -1, 1, 0, 0, 0] (0, -3)) = source194 := by
  decide +kernel

theorem source194_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source194 (momentValues f) = 0 := by
  rw [← source194_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source195 : Sparse := [([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, -1, -1, 0, 2, 0], 9), ([0, 1, -2, 0, 0, 1, 0], 18), ([0, 1, -1, -2, 0, 2, 0], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, -1, 2, 0], -9), ([0, 1, -1, -1, 0, 2, -1], 9), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 2, -1, -2, 0, 1, 0], 9), ([0, 2, -1, -1, -1, 1, 0], 9), ([0, 2, -1, -1, 0, 0, 0], 9), ([0, 2, -1, -1, 0, 1, -1], -9), ([1, 0, -1, -1, 0, 1, 1], 9), ([1, 0, -1, -1, 0, 2, 0], 9), ([1, 0, -1, -1, 1, 1, 0], -9), ([1, 0, 0, -1, 0, 1, 0], 9), ([1, 1, -2, 0, 0, 1, 0], 18), ([1, 1, -1, -2, 0, 1, 1], 9), ([1, 1, -1, -2, 1, 1, 0], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, 0, 0, 1], -9), ([1, 1, -1, -1, 0, 2, -1], 9), ([1, 1, -1, -1, 1, 0, 0], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, 0, -1, 0, 0, 0], 9), ([1, 2, -1, -1, -1, 1, 0], 9), ([1, 2, -1, -1, 0, 0, 0], 9)]

theorem source195_checked : normalize (row ![1, -1, -1, 0, 1, 0] ![0, 1, -1, 0, 0, 0] (3, 3)) = source195 := by
  decide +kernel

theorem source195_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source195 (momentValues f) = 0 := by
  rw [← source195_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source196 : Sparse := [([0, -2, 1, 1, 0, 1, -1], 9), ([0, -2, 1, 1, 1, 0, -1], 9), ([0, -1, 0, 1, 0, 1, -1], 9), ([0, -1, 1, 1, -1, 0, 0], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, -1, 1, 1, 0, 1, -2], -9), ([0, -1, 1, 1, 1, 0, -2], 9), ([0, -1, 1, 2, -1, 0, -1], 9), ([0, -1, 1, 2, 0, 0, -2], 9), ([0, -1, 2, 0, 0, 0, -1], 18), ([0, 0, 0, 1, 0, 0, -1], 9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 0, 1, 1, 0, -1, -1], 9), ([0, 0, 1, 1, 0, 0, -2], 9), ([1, -2, 1, 1, 0, 0, 0], -9), ([1, -2, 1, 1, 0, 1, -1], 9), ([1, -2, 1, 1, 1, 0, -1], 9), ([1, -2, 1, 2, 0, 0, -1], 9), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 1, 1, 1, 0, -2], 9), ([1, -1, 1, 2, 0, -1, -1], 9), ([1, -1, 2, 0, 0, 0, -1], 18), ([1, 0, 1, 1, 0, -1, -1], 9), ([1, 0, 1, 1, 0, 0, -2], 9)]

theorem source196_checked : normalize (row ![-1, 1, 1, 0, 0, -1] ![0, -1, 1, 0, 0, 0] (3, 3)) = source196 := by
  decide +kernel

theorem source196_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source196 (momentValues f) = 0 := by
  rw [← source196_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source197 : Sparse := [([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, 0, -1, 0, 0, 1], 9), ([0, 1, -1, -2, 0, 0, 2], 9), ([0, 1, -1, -2, 0, 1, 1], -9), ([0, 1, -1, -2, 1, 0, 1], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 0, -1, 2], -9), ([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 1, 0, -1, 0, 0, 0], -9), ([0, 2, -1, -2, 0, 0, 1], -9), ([0, 2, -1, -1, 0, 0, 0], 9), ([1, 0, -1, -1, 0, 0, 2], -9), ([1, 0, -1, -1, 0, 1, 1], -9), ([1, 1, -2, 0, 0, 0, 1], -18), ([1, 1, -1, -2, 0, 1, 1], -9), ([1, 1, -1, -1, -1, 0, 2], -9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 1, 0, 0], -9), ([1, 1, 0, -1, -1, 0, 1], -9), ([1, 1, 0, -1, 0, 0, 0], -9), ([1, 2, -1, -2, 0, 0, 1], -9), ([1, 2, -1, -1, -1, 0, 1], -9), ([1, 2, -1, -1, 0, -1, 1], -9), ([1, 2, -1, -1, 0, 0, 0], 9)]

theorem source197_checked : normalize (row ![1, -1, -1, 0, 0, 1] ![0, 1, -1, 0, 0, 0] (0, -3)) = source197 := by
  decide +kernel

theorem source197_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source197 (momentValues f) = 0 := by
  rw [← source197_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source198 : Sparse := [([0, -1, 1, 1, -1, 0, 0], 9), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 1, 1, -2, -1, 1], 9), ([0, 0, 1, 1, -2, 0, 0], 9), ([0, 0, 1, 1, -1, -2, 1], 9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 0, 1, 1, 0, -1, -1], 9), ([0, 0, 1, 2, -2, -1, 0], 9), ([0, 0, 1, 2, -1, -1, -1], 9), ([0, 0, 2, 0, -1, -1, 0], 18), ([0, 1, 0, 1, -1, -1, 0], 9), ([0, 1, 1, 1, -2, -1, 0], -9), ([0, 1, 1, 1, -1, -2, 0], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, -1, 1, 2, -1, -1, 0], 9), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 0, 0, 1, 0, -1, 0], 9), ([1, 0, 1, 1, -2, -1, 1], 9), ([1, 0, 1, 1, -2, 0, 0], 9), ([1, 0, 1, 1, -1, -2, 1], 9), ([1, 0, 1, 1, 0, -2, 0], -9), ([1, 0, 1, 1, 0, -1, -1], 9), ([1, 0, 1, 2, -1, -2, 0], 9), ([1, 0, 2, 0, -1, -1, 0], 18), ([1, 1, 1, 1, -1, -2, 0], 9), ([1, 1, 1, 1, -1, -1, -1], 9)]

theorem source198_checked : normalize (row ![0, 1, 1, -1, -1, 0] ![0, -1, 1, 0, 0, 0] (3, 3)) = source198 := by
  decide +kernel

theorem source198_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source198 (momentValues f) = 0 := by
  rw [← source198_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source199 : Sparse := [([0, -1, -1, -1, 2, 1, 0], -9), ([0, -1, 0, -1, 1, 1, 0], 9), ([0, 0, -1, -2, 1, 1, 1], 9), ([0, 0, -1, -2, 1, 2, 0], -9), ([0, 0, -1, -2, 2, 1, 0], 9), ([0, 0, -1, -1, 0, 2, 0], 9), ([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, 0, -1, 0, 1, 0], -9), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 1, -1, -2, 1, 1, 0], -9), ([0, 1, -1, -1, 1, 1, -1], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 1, 2, 0], -9), ([1, 0, -2, 0, 1, 1, 0], -18), ([1, 0, -1, -2, 1, 2, 0], -9), ([1, 0, -1, -1, 0, 1, 1], -9), ([1, 0, -1, -1, 0, 2, 0], 9), ([1, 0, -1, -1, 1, 2, -1], -9), ([1, 0, -1, -1, 2, 0, 0], -9), ([1, 0, -1, -1, 2, 1, -1], -9), ([1, 0, 0, -1, 0, 1, 0], -9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 1, -1, -2, 1, 1, 0], -9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, -1, -1, 1, 0, 0], -9), ([1, 1, -1, -1, 1, 1, -1], 9)]

theorem source199_checked : normalize (row ![0, -1, -1, 1, 1, 0] ![0, 1, -1, 0, 0, 0] (0, -3)) = source199 := by
  decide +kernel

theorem source199_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source199 (momentValues f) = 0 := by
  rw [← source199_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
