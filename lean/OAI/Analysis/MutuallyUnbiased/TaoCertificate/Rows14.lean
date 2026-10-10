import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source112 : Sparse := [([0, 0, 0, 1, -1, 1, -1], -36), ([0, 0, 0, 2, -1, 0, -1], -36), ([0, 0, 1, 1, -1, 0, -1], 36), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, 0, 1, -1, -1, 0], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 1, 0, 1, 0, 0, -2], -36), ([0, 1, 0, 2, -2, 0, -1], -36), ([0, 1, 0, 2, -1, 0, -2], 36), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 1, 1, -1, -1, -1], -36), ([0, 2, 0, 1, -1, 0, -2], -36), ([1, 0, 0, 2, -1, 0, -1], -36), ([1, 0, 1, 1, -1, 0, -1], 36), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, -1, 1, -1, 1, -1], 36), ([1, 1, 0, 0, -1, 1, -1], -36), ([1, 1, 0, 1, -2, 0, 0], 36), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 1, 0, 1, 0, 0, -2], -36), ([1, 1, 0, 2, -1, 0, -2], 36), ([1, 1, 1, 1, -1, -1, -1], -36), ([1, 2, 0, 0, -1, 0, -1], 36), ([1, 2, 0, 1, -2, 0, -1], -36)]

theorem source112_checked : normalize (row ![1, 0, 1, -1, 0, -1] ![1, 0, 1, -1, 0, -1] (-12, 0)) = source112 := by
  decide +kernel

theorem source112_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source112 (momentValues f) = 0 := by
  rw [← source112_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source113 : Sparse := [([0, 0, 0, 1, 1, -1, -1], -36), ([0, 0, 0, 2, 0, -1, -1], -36), ([0, 0, 1, 1, 0, -1, -1], -36), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, -1, 1, 0, 0, -1], -36), ([0, 1, -1, 1, 1, -1, -1], -36), ([0, 1, 0, 0, 1, -1, -1], -36), ([0, 1, 0, 1, -1, -1, 0], -36), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 1, 0, 1, 0, -2, 0], -36), ([0, 1, 0, 1, 0, 0, -2], -36), ([0, 1, 0, 2, 0, -2, -1], -36), ([0, 1, 0, 2, 0, -1, -2], -36), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 1, 1, -1, -1, -1], -36), ([0, 2, 0, 0, 0, -1, -1], -36), ([0, 2, 0, 1, 0, -2, -1], -36), ([0, 2, 0, 1, 0, -1, -2], -36), ([1, 0, 0, 2, 0, -1, -1], -36), ([1, 1, -1, 1, 1, -1, -1], -36), ([1, 1, 0, 1, 0, -2, 0], -36), ([1, 1, 0, 1, 0, 0, -2], -36), ([1, 1, 1, 1, -1, -1, -1], -36), ([1, 2, 0, 0, 0, -1, -1], -36)]

theorem source113_checked : normalize (row ![1, 0, 1, 0, -1, -1] ![1, 0, 1, 0, -1, -1] (-12, 0)) = source113 := by
  decide +kernel

theorem source113_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source113 (momentValues f) = 0 := by
  rw [← source113_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source114 : Sparse := [([0, 0, 1, -1, -1, 0, 1], -36), ([0, 1, 0, -1, -1, 0, 1], 36), ([0, 1, 0, -1, -1, 1, 0], -36), ([0, 1, 1, -1, -1, -1, 1], -36), ([0, 1, 1, -1, 0, -1, 0], -36), ([0, 1, 1, 0, -2, 0, 0], -36), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 2, -1, -2, 0, 0], -36), ([0, 2, 0, -1, -1, 0, 0], -36), ([0, 2, 1, -2, -1, 0, 0], -36), ([0, 2, 1, -1, -2, 0, 0], 36), ([1, 0, 1, -1, -1, 1, 0], -36), ([1, 0, 2, -1, -1, 0, 0], 36), ([1, 1, 0, -1, -1, 0, 1], 36), ([1, 1, 1, -2, 0, 0, 0], 36), ([1, 1, 1, -1, -1, -1, 1], -36), ([1, 1, 1, -1, -1, 1, -1], 36), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, 0, -2, 0, 0], -36), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 1, 2, -2, -1, 0, 0], -36), ([1, 2, 0, -1, -1, 0, 0], -36), ([1, 2, 1, -1, -2, 0, 0], 36)]

theorem source114_checked : normalize (row ![1, 1, -1, -1, 0, 0] ![1, 1, -1, -1, 0, 0] (-12, 0)) = source114 := by
  decide +kernel

theorem source114_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source114 (momentValues f) = 0 := by
  rw [← source114_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source115 : Sparse := [([0, 0, 1, -1, 0, -1, 1], 36), ([0, 0, 1, -1, 1, -1, 0], -36), ([0, 0, 2, -1, 0, -1, 0], -36), ([0, 1, 0, -1, 0, -1, 1], -36), ([0, 1, 1, -1, -1, -1, 1], -36), ([0, 1, 1, -1, -1, 0, 0], -36), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 1, 1, 0, 0, -2, 0], -36), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 2, -2, 0, -1, 0], -36), ([0, 1, 2, -1, 0, -2, 0], 36), ([0, 2, 1, -1, 0, -2, 0], -36), ([1, 0, 1, -1, 0, -1, 1], 36), ([1, 0, 2, -1, 0, -1, 0], -36), ([1, 1, 0, -1, 1, -1, 0], -36), ([1, 1, 1, -2, 0, 0, 0], 36), ([1, 1, 1, -1, -1, -1, 1], -36), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, -1, 1, -1, -1], 36), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 1, 1, 0, 0, -2, 0], -36), ([1, 1, 2, -1, 0, -2, 0], 36), ([1, 2, 0, -1, 0, -1, 0], 36), ([1, 2, 1, -2, 0, -1, 0], -36)]

theorem source115_checked : normalize (row ![1, 1, -1, 0, -1, 0] ![1, 1, -1, 0, -1, 0] (-12, 0)) = source115 := by
  decide +kernel

theorem source115_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source115 (momentValues f) = 0 := by
  rw [← source115_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source116 : Sparse := [([0, 0, 1, -1, 0, 1, -1], -36), ([0, 0, 1, -1, 1, 0, -1], -36), ([0, 1, 0, -1, 0, 1, -1], -36), ([0, 1, 0, -1, 1, 0, -1], -36), ([0, 1, 1, -1, -1, 0, 0], -36), ([0, 1, 1, -1, 0, -1, 0], -36), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 2, -2, 0, 0, -1], -36), ([0, 1, 2, -1, 0, 0, -2], -36), ([0, 2, 1, -2, 0, 0, -1], -36), ([0, 2, 1, -1, 0, 0, -2], -36), ([1, 0, 2, -1, 0, 0, -1], 36), ([1, 1, 1, -2, 0, 0, 0], 36), ([1, 1, 1, -1, -1, 1, -1], 36), ([1, 1, 1, -1, 1, -1, -1], 36), ([1, 1, 1, 0, 0, 0, -2], 36), ([1, 2, 0, -1, 0, 0, -1], 36)]

theorem source116_checked : normalize (row ![1, 1, -1, 0, 0, -1] ![1, 1, -1, 0, 0, -1] (-12, 0)) = source116 := by
  decide +kernel

theorem source116_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source116 (momentValues f) = 0 := by
  rw [← source116_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source117 : Sparse := [([0, 0, 1, 0, -1, -1, 1], -36), ([0, 0, 1, 1, -1, -1, 0], -36), ([0, 0, 2, 0, -1, -1, 0], -36), ([0, 1, 0, 0, -1, -1, 1], -36), ([0, 1, 0, 1, -1, -1, 0], -36), ([0, 1, 1, -1, -1, -1, 1], -36), ([0, 1, 1, -1, -1, 0, 0], -36), ([0, 1, 1, -1, 0, -1, 0], -36), ([0, 1, 1, 0, -2, 0, 0], -36), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 1, 0, 0, -2, 0], -36), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 1, 1, -1, -1, -1], -36), ([0, 1, 2, 0, -2, -1, 0], -36), ([0, 1, 2, 0, -1, -2, 0], -36), ([0, 2, 0, 0, -1, -1, 0], -36), ([0, 2, 1, 0, -2, -1, 0], -36), ([0, 2, 1, 0, -1, -2, 0], -36), ([1, 0, 2, 0, -1, -1, 0], -36), ([1, 1, 1, -1, -1, -1, 1], -36), ([1, 1, 1, 0, -2, 0, 0], -36), ([1, 1, 1, 0, 0, -2, 0], -36), ([1, 1, 1, 1, -1, -1, -1], -36), ([1, 2, 0, 0, -1, -1, 0], -36)]

theorem source117_checked : normalize (row ![1, 1, 0, -1, -1, 0] ![1, 1, 0, -1, -1, 0] (-12, 0)) = source117 := by
  decide +kernel

theorem source117_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source117 (momentValues f) = 0 := by
  rw [← source117_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source118 : Sparse := [([0, 0, 1, 0, -1, 1, -1], -36), ([0, 0, 1, 1, -1, 0, -1], 36), ([0, 0, 2, 0, -1, 0, -1], -36), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 1, 1, -1, -1, 0, 0], -36), ([0, 1, 1, 0, -2, 0, 0], -36), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 1, 1, 1, -1, -1, -1], -36), ([0, 1, 2, 0, -2, 0, -1], 36), ([0, 1, 2, 0, -1, 0, -2], -36), ([0, 2, 1, 0, -2, 0, -1], -36), ([1, 0, 1, 1, -1, 0, -1], 36), ([1, 0, 2, 0, -1, 0, -1], -36), ([1, 1, 0, 0, -1, 1, -1], -36), ([1, 1, 1, -1, -1, 1, -1], 36), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, 0, -2, 0, 0], -36), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 1, 1, 0, 0, 0, -2], 36), ([1, 1, 1, 1, -1, -1, -1], -36), ([1, 1, 2, 0, -2, 0, -1], 36), ([1, 2, 0, 0, -1, 0, -1], 36), ([1, 2, 1, 0, -1, 0, -2], -36)]

theorem source118_checked : normalize (row ![1, 1, 0, -1, 0, -1] ![1, 1, 0, -1, 0, -1] (-12, 0)) = source118 := by
  decide +kernel

theorem source118_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source118 (momentValues f) = 0 := by
  rw [← source118_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source119 : Sparse := [([0, 0, 1, 1, 0, -1, -1], -36), ([0, 1, 0, 0, 1, -1, -1], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 1, 1, -1, 0, -1, 0], -36), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 1, 1, 0, 0, -2, 0], -36), ([0, 1, 1, 1, -1, -1, -1], -36), ([0, 1, 2, 0, 0, -2, -1], -36), ([0, 2, 0, 0, 0, -1, -1], -36), ([0, 2, 1, 0, 0, -2, -1], 36), ([0, 2, 1, 0, 0, -1, -2], -36), ([1, 0, 1, 0, 1, -1, -1], -36), ([1, 0, 2, 0, 0, -1, -1], 36), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, -1, 1, -1, -1], 36), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 1, 1, 0, 0, -2, 0], -36), ([1, 1, 1, 0, 0, 0, -2], 36), ([1, 1, 1, 1, -1, -1, -1], -36), ([1, 1, 2, 0, 0, -1, -2], -36), ([1, 2, 0, 0, 0, -1, -1], -36), ([1, 2, 1, 0, 0, -2, -1], 36)]

theorem source119_checked : normalize (row ![1, 1, 0, 0, -1, -1] ![1, 1, 0, 0, -1, -1] (-12, 0)) = source119 := by
  decide +kernel

theorem source119_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source119 (momentValues f) = 0 := by
  rw [← source119_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
