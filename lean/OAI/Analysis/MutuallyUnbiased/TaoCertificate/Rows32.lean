import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source256 : Sparse := [([0, -2, 1, 1, 1, 0, -1], -9), ([0, -2, 2, 1, 0, 0, -1], 9), ([0, -1, 1, 0, 0, 0, 0], 9), ([0, -1, 1, 0, 0, 1, -1], -9), ([0, -1, 1, 0, 1, 0, -1], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 2, 1, -1, 0, -1], -9), ([0, -1, 2, 1, 0, -1, -1], 9), ([0, -1, 2, 1, 0, 0, -2], -9), ([0, 0, 1, 0, 0, 0, -1], -9), ([0, 0, 1, 1, 0, 0, -2], 9), ([1, -2, 1, 1, 0, 0, 0], -9), ([1, -2, 1, 1, 0, 1, -1], -9), ([1, -1, 0, 2, 0, 0, -1], -18), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, 1, -2], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 1, 1, 1, 0, -2], -9), ([1, -1, 2, 1, -1, 0, -1], -9), ([1, -1, 2, 1, 0, 0, -2], -9), ([1, 0, 1, 0, 0, 0, -1], -9), ([1, 0, 1, 1, -1, 0, -1], -9), ([1, 0, 1, 1, 0, -1, -1], -9), ([1, 0, 1, 1, 0, 0, -2], 9)]

theorem source256_checked : normalize (row ![-1, 1, 1, 0, 0, -1] ![0, 1, -1, 0, 0, 0] (0, -3)) = source256 := by
  decide +kernel

theorem source256_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source256 (momentValues f) = 0 := by
  rw [← source256_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source257 : Sparse := [([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, -1, -1, 1, 0, 1], 9), ([0, 1, -2, -1, 0, 1, 1], 9), ([0, 1, -1, -1, -1, 0, 2], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 0, -1, 2], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, -1, 0, -1, 0, 1], 9), ([0, 1, -1, 0, 0, 0, 0], 9), ([0, 1, 0, -2, 0, 0, 1], 18), ([0, 2, -2, -1, 0, 0, 1], 9), ([0, 2, -1, -1, -1, 0, 1], -9), ([0, 2, -1, -1, 0, -1, 1], 9), ([0, 2, -1, -1, 0, 0, 0], 9), ([1, 0, -1, -1, 0, 0, 2], -9), ([1, 0, -1, -1, 0, 1, 1], 9), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, -1, 0, 0, 0, 1], 9), ([1, 1, -2, -1, 0, 0, 2], 9), ([1, 1, -2, -1, 1, 0, 1], 9), ([1, 1, -1, -1, -1, 0, 2], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, 0, -1, 2], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 1, 0, 0], 9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, 0, -2, 0, 0, 1], 18), ([1, 2, -1, -1, 0, -1, 1], 9), ([1, 2, -1, -1, 0, 0, 0], 9)]

theorem source257_checked : normalize (row ![1, -1, -1, 0, 0, 1] ![0, -1, 1, 0, 0, 0] (3, 3)) = source257 := by
  decide +kernel

theorem source257_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source257 (momentValues f) = 0 := by
  rw [← source257_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source258 : Sparse := [([0, -1, 1, 1, 0, -1, 0], -9), ([0, -1, 2, 1, -1, -1, 0], 9), ([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 1, 0, -1, 0, 0], -9), ([0, 0, 1, 0, 0, -1, 0], 9), ([0, 0, 1, 1, -2, 0, 0], 9), ([0, 0, 1, 1, -1, -2, 1], -9), ([0, 0, 2, 1, -2, -1, 0], -9), ([0, 0, 2, 1, -1, -2, 0], 9), ([0, 0, 2, 1, -1, -1, -1], -9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 1, 1, 1, -1, -1, -1], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, -1, 0, 0], -9), ([1, 0, 0, 2, -1, -1, 0], -18), ([1, 0, 1, 0, -1, 0, 0], -9), ([1, 0, 1, 1, -2, -1, 1], -9), ([1, 0, 1, 1, -2, 0, 0], 9), ([1, 0, 1, 1, -1, 0, -1], -9), ([1, 0, 1, 1, 0, -2, 0], -9), ([1, 0, 1, 1, 0, -1, -1], -9), ([1, 0, 2, 1, -2, -1, 0], -9), ([1, 0, 2, 1, -1, -1, -1], -9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 1, 1, 1, -2, -1, 0], -9), ([1, 1, 1, 1, -1, -2, 0], -9), ([1, 1, 1, 1, -1, -1, -1], 9)]

theorem source258_checked : normalize (row ![0, 1, 1, -1, -1, 0] ![0, 1, -1, 0, 0, 0] (0, -3)) = source258 := by
  decide +kernel

theorem source258_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source258 (momentValues f) = 0 := by
  rw [← source258_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source259 : Sparse := [([0, -1, -1, -1, 1, 2, 0], 9), ([0, -1, -1, -1, 2, 1, 0], 9), ([0, 0, -2, -1, 1, 2, 0], 9), ([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, -1, -1, 0, 2, 0], 9), ([0, 0, -1, -1, 1, 0, 1], 9), ([0, 0, -1, -1, 1, 2, -1], -9), ([0, 0, -1, -1, 2, 1, -1], 9), ([0, 0, -1, 0, 0, 1, 0], 9), ([0, 0, -1, 0, 1, 1, -1], 9), ([0, 0, 0, -2, 1, 1, 0], 18), ([0, 1, -2, -1, 1, 1, 0], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 1, 2, 0], 9), ([1, -1, -1, -1, 2, 1, 0], 9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, 0, -2, -1, 1, 1, 1], 9), ([1, 0, -2, -1, 2, 1, 0], 9), ([1, 0, -1, -1, 0, 1, 1], 9), ([1, 0, -1, -1, 0, 2, 0], 9), ([1, 0, -1, -1, 1, 0, 1], 9), ([1, 0, -1, -1, 2, 0, 0], -9), ([1, 0, -1, -1, 2, 1, -1], 9), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, 0, -2, 1, 1, 0], 18), ([1, 1, -1, -1, 1, 0, 0], 9), ([1, 1, -1, -1, 1, 1, -1], 9)]

theorem source259_checked : normalize (row ![0, -1, -1, 1, 1, 0] ![0, -1, 1, 0, 0, 0] (3, 3)) = source259 := by
  decide +kernel

theorem source259_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source259 (momentValues f) = 0 := by
  rw [← source259_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source260 : Sparse := [([0, -1, 1, 1, -1, 0, 0], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, 0, 0, 2, -1, 0, -1], 18), ([0, 0, 1, 0, -1, 1, -1], 9), ([0, 0, 1, 1, -2, 0, 0], 9), ([0, 0, 1, 1, -2, 1, -1], -9), ([0, 0, 1, 1, -1, 1, -2], 9), ([0, 0, 1, 1, 0, -1, -1], 9), ([0, 0, 1, 1, 0, 0, -2], 9), ([0, 0, 2, 1, -2, 0, -1], 9), ([0, 0, 2, 1, -1, 0, -2], 9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 1, 1, 1, -2, 0, -1], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, -1, 0, -2], -9), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, 0, -1], -9), ([1, -1, 2, 1, -1, 0, -1], 9), ([1, 0, 0, 2, -1, 0, -1], 18), ([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 1, 0, 0, 0, -1], 9), ([1, 0, 1, 1, -2, 0, 0], 9), ([1, 0, 1, 1, -1, -1, 0], -9), ([1, 0, 1, 1, -1, 1, -2], 9), ([1, 0, 1, 1, 0, -1, -1], 9), ([1, 0, 1, 1, 0, 0, -2], 9), ([1, 0, 2, 1, -1, -1, -1], 9), ([1, 1, 1, 1, -2, 0, -1], 9), ([1, 1, 1, 1, -1, -1, -1], 9)]

theorem source260_checked : normalize (row ![0, 1, 1, -1, 0, -1] ![0, 1, -1, 0, 0, 0] (3, 3)) = source260 := by
  decide +kernel

theorem source260_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source260 (momentValues f) = 0 := by
  rw [← source260_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source261 : Sparse := [([0, -1, -1, -1, 1, 0, 2], -9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, 0, -2, -1, 1, 0, 2], 9), ([0, 0, -2, -1, 1, 1, 1], -9), ([0, 0, -2, -1, 2, 0, 1], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, -1, -1, 2, -1, 1], -9), ([0, 0, -1, 0, 0, 0, 1], -9), ([0, 0, -1, 0, 1, -1, 1], 9), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 1, -2, -1, 1, 0, 1], -9), ([0, 1, -1, -1, 0, 0, 1], 9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, -1, 2, 0, 1], -9), ([1, 0, -2, -1, 1, 1, 1], -9), ([1, 0, -1, -1, 0, 0, 2], -9), ([1, 0, -1, -1, 0, 1, 1], -9), ([1, 0, -1, -1, 1, -1, 2], -9), ([1, 0, -1, -1, 1, 1, 0], 9), ([1, 0, -1, -1, 2, 0, 0], -9), ([1, 0, -1, 0, 0, 0, 1], -9), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, 0, -2, 1, 0, 1], -18), ([1, 1, -2, -1, 1, 0, 1], -9), ([1, 1, -1, -1, 0, 0, 1], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 1, 0, 0], -9)]

theorem source261_checked : normalize (row ![0, -1, -1, 1, 0, 1] ![0, -1, 1, 0, 0, 0] (0, -3)) = source261 := by
  decide +kernel

theorem source261_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source261 (momentValues f) = 0 := by
  rw [← source261_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source262 : Sparse := [([0, -1, 1, 1, 0, -1, 0], 9), ([0, -1, 1, 1, 0, 0, -1], 9), ([0, 0, 0, 2, 0, -1, -1], 18), ([0, 0, 1, 0, 0, 0, -1], 9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 0, 1, 1, -1, 0, -1], -9), ([0, 0, 1, 1, 0, 0, -2], 9), ([0, 0, 1, 1, 1, -2, -1], 9), ([0, 0, 1, 1, 1, -1, -2], 9), ([0, 0, 2, 1, -1, -1, -1], 9), ([0, 0, 2, 1, 0, -1, -2], 9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, 0, -2, -1], 9), ([0, 1, 1, 1, 0, -1, -2], -9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 2, 1, 0, -1, -1], 9), ([1, 0, 0, 2, 0, -1, -1], 18), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 1, 0, 1, -1, -1], 9), ([1, 0, 1, 1, -1, -1, 0], 9), ([1, 0, 1, 1, 0, -2, 0], -9), ([1, 0, 1, 1, 0, 0, -2], 9), ([1, 0, 1, 1, 1, -2, -1], 9), ([1, 0, 1, 1, 1, -1, -2], 9), ([1, 0, 2, 1, 0, -2, -1], 9), ([1, 1, 1, 1, -1, -1, -1], 9), ([1, 1, 1, 1, 0, -2, -1], 9)]

theorem source262_checked : normalize (row ![0, 1, 1, 0, -1, -1] ![0, 1, -1, 0, 0, 0] (3, 3)) = source262 := by
  decide +kernel

theorem source262_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source262 (momentValues f) = 0 := by
  rw [← source262_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source263 : Sparse := [([0, -1, -1, -1, 0, 1, 2], -9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, 0, -2, -1, 0, 1, 2], 9), ([0, 0, -2, -1, 0, 2, 1], -9), ([0, 0, -2, -1, 1, 1, 1], 9), ([0, 0, -1, -1, 0, 2, 0], 9), ([0, 0, -1, -1, 1, 0, 1], -9), ([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, -1, 0, 0, 0, 1], 9), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 1, -2, -1, 0, 1, 1], -9), ([0, 1, -1, -1, -1, 1, 1], 9), ([1, -1, -1, -1, 0, 2, 1], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, 0, -2, -1, 0, 2, 1], -9), ([1, 0, -1, -1, -1, 1, 2], -9), ([1, 0, -1, -1, -1, 2, 1], -9), ([1, 0, -1, -1, 0, 0, 2], -9), ([1, 0, -1, -1, 0, 2, 0], 9), ([1, 0, -1, -1, 1, 1, 0], -9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, 0, -2, 0, 1, 1], -18), ([1, 1, -2, -1, 0, 1, 1], -9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, 0, 0, 1], -9), ([1, 1, -1, -1, 0, 1, 0], -9)]

theorem source263_checked : normalize (row ![0, -1, -1, 0, 1, 1] ![0, -1, 1, 0, 0, 0] (0, -3)) = source263 := by
  decide +kernel

theorem source263_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source263 (momentValues f) = 0 := by
  rw [← source263_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
