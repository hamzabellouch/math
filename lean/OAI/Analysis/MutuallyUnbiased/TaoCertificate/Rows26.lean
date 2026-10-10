import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source208 : Sparse := [([0, -2, 1, 0, 1, 0, 0], 9), ([0, -2, 1, 0, 1, 1, -1], -9), ([0, -2, 1, 0, 2, 0, -1], 9), ([0, -2, 1, 1, 1, 0, -1], 9), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, -1, 0, 0, 1, 1, -1], 9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, -1, 2, 0, -1], 9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, -1, 1, 0, 1, 1, -2], 9), ([0, -1, 1, 1, 1, 0, -2], 9), ([0, -1, 2, 0, 0, 0, -1], 18), ([0, 0, 1, -1, 1, 0, -1], 9), ([0, 0, 1, 0, 1, -1, -1], 9), ([1, -2, 1, 0, 1, 0, 0], 9), ([1, -2, 1, 1, 1, 0, -1], 9), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, -1, 1, 0, 1, 1, -2], 9), ([1, -1, 1, 0, 2, -1, -1], 9), ([1, -1, 1, 0, 2, 0, -2], 9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 1, 1, 1, 0, -2], 9), ([1, -1, 2, 0, 0, 0, -1], 18), ([1, 0, 0, 0, 1, 0, -1], 9), ([1, 0, 1, -1, 1, 0, -1], 9), ([1, 0, 1, 0, 1, -1, -1], 9), ([1, 0, 1, 0, 1, 0, -2], -9)]

theorem source208_checked : normalize (row ![-1, 1, 0, 1, 0, -1] ![0, -1, 0, 1, 0, 0] (3, 3)) = source208 := by
  decide +kernel

theorem source208_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source208 (momentValues f) = 0 := by
  rw [← source208_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source209 : Sparse := [([0, 0, -1, 0, -1, 0, 2], 9), ([0, 0, 0, 0, -1, 0, 1], -9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, 0, -2, 0, 2], -9), ([0, 1, -1, 0, -2, 1, 1], -9), ([0, 1, -1, 1, -2, 0, 1], 9), ([0, 1, -1, 1, -1, 0, 0], -9), ([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 0, 0, -1, -1, 1], 9), ([0, 1, 0, 0, -1, 0, 0], 9), ([0, 2, -1, 0, -2, 0, 1], 9), ([0, 2, -1, 0, -1, -1, 1], -9), ([1, 0, -1, 0, -1, 0, 2], 9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, 0, 0, -1, 0, 1], -9), ([1, 1, -2, 0, 0, 0, 1], -18), ([1, 1, -1, -1, -1, 0, 2], -9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, 0, -2, 0, 2], -9), ([1, 1, -1, 0, -2, 1, 1], -9), ([1, 1, -1, 0, -1, -1, 2], -9), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, 0, -1, -1, 0, 1], -9), ([1, 2, -1, -1, -1, 0, 1], -9), ([1, 2, -1, 0, -1, 0, 0], -9)]

theorem source209_checked : normalize (row ![1, -1, 0, -1, 0, 1] ![0, 1, 0, -1, 0, 0] (0, -3)) = source209 := by
  decide +kernel

theorem source209_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source209 (momentValues f) = 0 := by
  rw [← source209_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source210 : Sparse := [([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, -1, 1, -1, 2, -1, 0], 9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 1, -2, 1, -1, 1], -9), ([0, 0, 1, -2, 1, 0, 0], 9), ([0, 0, 1, -2, 2, -1, 0], 9), ([0, 0, 1, -1, 1, -2, 1], 9), ([0, 0, 1, -1, 1, 0, -1], 9), ([0, 0, 1, 0, 1, -1, -1], 9), ([0, 0, 2, -1, 0, -1, 0], 18), ([0, 1, 1, -2, 1, -1, 0], 9), ([0, 1, 1, -1, 1, -2, 0], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, 0, 0, 0, 1, -1, 0], 9), ([1, 0, 1, -2, 1, 0, 0], 9), ([1, 0, 1, -1, 1, -2, 1], 9), ([1, 0, 1, -1, 1, 0, -1], 9), ([1, 0, 1, -1, 2, -2, 0], 9), ([1, 0, 1, -1, 2, -1, -1], 9), ([1, 0, 1, 0, 1, -2, 0], -9), ([1, 0, 1, 0, 1, -1, -1], 9), ([1, 0, 2, -1, 0, -1, 0], 18), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 1, 1, -2, 1, -1, 0], 9), ([1, 1, 1, -1, 1, -2, 0], 9), ([1, 1, 1, -1, 1, -1, -1], -9)]

theorem source210_checked : normalize (row ![0, 1, -1, 1, -1, 0] ![0, -1, 0, 1, 0, 0] (3, 3)) = source210 := by
  decide +kernel

theorem source210_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source210 (momentValues f) = 0 := by
  rw [← source210_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source211 : Sparse := [([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, 0, -1, 0, -1, 2, 0], 9), ([0, 0, -1, 1, -2, 1, 1], -9), ([0, 0, -1, 1, -2, 2, 0], -9), ([0, 0, -1, 2, -2, 1, 0], 9), ([0, 0, -1, 2, -1, 1, -1], -9), ([0, 0, 0, 0, -1, 1, 0], -9), ([0, 0, 0, 1, -1, 0, 0], 9), ([0, 0, 0, 1, -1, 1, -1], 9), ([0, 1, -1, 1, -2, 1, 0], 9), ([0, 1, -1, 1, -1, 0, 0], -9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, -1, 2, 0], -9), ([1, -1, -1, 2, -1, 1, 0], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, 0, -2, 1, 0, 1, 0], -18), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, -1, 0, -1, 2, 0], 9), ([1, 0, -1, 1, -2, 1, 1], -9), ([1, 0, -1, 1, -2, 2, 0], -9), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, -1, 1, -1, 2, -1], -9), ([1, 0, -1, 2, -1, 0, 0], -9), ([1, 0, 0, 0, -1, 1, 0], -9), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 1, -1, 1, -1], -9)]

theorem source211_checked : normalize (row ![0, -1, 1, -1, 1, 0] ![0, 1, 0, -1, 0, 0] (0, -3)) = source211 := by
  decide +kernel

theorem source211_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source211 (momentValues f) = 0 := by
  rw [← source211_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source212 : Sparse := [([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, -1, 2, 0, -1], -9), ([0, 0, 0, -1, 1, 0, 0], -9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 0, 0, 0, 1, 0, -1], 9), ([0, 0, 1, -2, 1, 0, 0], 9), ([0, 0, 1, -2, 2, 0, -1], -9), ([0, 0, 1, -1, 2, -1, -1], 9), ([0, 0, 1, -1, 2, 0, -2], 9), ([0, 0, 1, 0, 1, -1, -1], -9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 1, 1, -1, 1, 0, -2], -9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, -1, 2, 0, -1], -9), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, 0, 0, -1, 1, 0, 0], -9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 0, 1, -2, 1, 0, 0], 9), ([1, 0, 1, -2, 1, 1, -1], -9), ([1, 0, 1, -2, 2, 0, -1], -9), ([1, 0, 1, -1, 1, -1, 0], -9), ([1, 0, 1, -1, 1, 1, -2], -9), ([1, 0, 1, 0, 1, 0, -2], -9), ([1, 0, 2, -1, 0, 0, -1], -18), ([1, 1, 1, -2, 1, 0, -1], -9), ([1, 1, 1, -1, 1, -1, -1], -9)]

theorem source212_checked : normalize (row ![0, 1, -1, 1, 0, -1] ![0, -1, 0, 1, 0, 0] (0, -3)) = source212 := by
  decide +kernel

theorem source212_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source212 (momentValues f) = 0 := by
  rw [← source212_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source213 : Sparse := [([0, -1, -1, 1, -1, 0, 2], -9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 2, -1, 0, 1], 9), ([0, -1, 0, 1, -1, 0, 1], 9), ([0, 0, -2, 1, 0, 0, 1], 18), ([0, 0, -1, 0, -1, 0, 2], 9), ([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, -1, 1, -2, 0, 2], 9), ([0, 0, -1, 1, -2, 1, 1], 9), ([0, 0, -1, 1, -1, -1, 2], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, -1, 2, -1, -1, 1], 9), ([0, 0, 0, 0, -1, 0, 1], 9), ([0, 1, -1, 0, -1, 0, 1], 9), ([0, 1, -1, 1, -1, 0, 0], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 2, -1, 0, 1], 9), ([1, 0, -2, 1, 0, 0, 1], 18), ([1, 0, -1, 0, -1, 0, 2], 9), ([1, 0, -1, 1, -1, -1, 2], 9), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 0, -1, 2, -2, 0, 1], 9), ([1, 0, -1, 2, -1, -1, 1], 9), ([1, 0, -1, 2, -1, 0, 0], -9), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 0, 0, 1, -1, 0, 0], 9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 1, -2, 0, 1], 9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, -1, 0, 0], 9)]

theorem source213_checked : normalize (row ![0, -1, 1, -1, 0, 1] ![0, 1, 0, -1, 0, 0] (3, 3)) = source213 := by
  decide +kernel

theorem source213_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source213 (momentValues f) = 0 := by
  rw [← source213_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source214 : Sparse := [([0, -1, 1, 0, 1, 0, -1], 9), ([0, -1, 1, 0, 2, -1, -1], -9), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 0, 0, 1, 1, -1, -1], 9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 0, 1, -1, 2, -1, -1], -9), ([0, 0, 1, 0, 2, -2, -1], 9), ([0, 0, 1, 0, 2, -1, -2], 9), ([0, 0, 1, 1, 1, -2, -1], -9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 1, 1, 0, 1, -1, -2], -9), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, -1, 1, 0, 1, 0, -1], 9), ([1, -1, 1, 0, 2, -1, -1], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 0, 0, 0, 1, 0, -1], -9), ([1, 0, 1, -1, 1, -1, 0], 9), ([1, 0, 1, -1, 1, 0, -1], -9), ([1, 0, 1, -1, 2, -1, -1], -9), ([1, 0, 1, 0, 1, -2, 0], -9), ([1, 0, 1, 0, 1, 0, -2], -9), ([1, 0, 1, 1, 1, -1, -2], -9), ([1, 0, 2, 0, 0, -1, -1], -18), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, 1, -2, -1], -9)]

theorem source214_checked : normalize (row ![0, 1, 0, 1, -1, -1] ![0, -1, 0, 1, 0, 0] (0, -3)) = source214 := by
  decide +kernel

theorem source214_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source214 (momentValues f) = 0 := by
  rw [← source214_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source215 : Sparse := [([0, -1, -1, 0, -1, 1, 2], -9), ([0, -1, -1, 0, -1, 2, 1], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, 0, -2, 0, 0, 1, 1], 18), ([0, 0, -1, -1, -1, 1, 2], 9), ([0, 0, -1, -1, -1, 2, 1], -9), ([0, 0, -1, 0, -2, 1, 2], 9), ([0, 0, -1, 0, -2, 2, 1], 9), ([0, 0, -1, 0, -1, 0, 2], 9), ([0, 0, -1, 0, -1, 2, 0], 9), ([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, 0, -1, -1, 1, 1], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, 0, -1, 1, 0], 9), ([1, -1, -1, 0, -1, 2, 1], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, 0, -2, 0, 0, 1, 1], 18), ([1, 0, -1, -1, -1, 1, 2], 9), ([1, 0, -1, 0, -1, 0, 2], 9), ([1, 0, -1, 0, -1, 2, 0], 9), ([1, 0, -1, 1, -2, 1, 1], 9), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, 0, -2, 1, 1], 9), ([1, 1, -1, 0, -1, 0, 1], -9), ([1, 1, -1, 0, -1, 1, 0], 9)]

theorem source215_checked : normalize (row ![0, -1, 0, -1, 1, 1] ![0, 1, 0, -1, 0, 0] (3, 3)) = source215 := by
  decide +kernel

theorem source215_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source215 (momentValues f) = 0 := by
  rw [← source215_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
