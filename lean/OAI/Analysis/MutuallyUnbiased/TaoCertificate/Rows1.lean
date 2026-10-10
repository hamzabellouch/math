import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source8 : Sparse := [([0, -1, -2, 2, 0, 0, 1], 18), ([0, -1, -2, 2, 0, 1, 0], 18), ([0, -1, -2, 2, 1, 0, 0], -18), ([0, -1, -1, 2, 0, 0, 0], 18), ([0, 0, -3, 3, 0, 0, 0], 36), ([0, 0, -2, 1, 0, 0, 1], 18), ([0, 0, -2, 1, 1, 0, 0], 18), ([0, 0, -2, 2, -1, 0, 1], 18), ([0, 0, -2, 2, 0, -1, 1], -18), ([0, 0, -2, 2, 0, 1, -1], 18), ([0, 0, -2, 2, 1, -1, 0], 18), ([0, 0, -2, 2, 1, 0, -1], 18), ([0, 0, -1, 2, 0, -1, 0], 18), ([0, 1, -2, 2, -1, 0, 0], 18), ([0, 1, -2, 2, 0, -1, 0], 18), ([1, -1, -2, 2, 1, 0, 0], -18), ([1, -1, -1, 2, 0, 0, 0], 18), ([1, 0, -2, 1, 0, 0, 1], 18), ([1, 0, -2, 1, 0, 1, 0], -18), ([1, 0, -2, 1, 1, 0, 0], 18), ([1, 0, -2, 2, -1, 1, 0], 18), ([1, 0, -2, 2, 0, -1, 1], -18), ([1, 0, -1, 2, -1, 0, 0], -18), ([1, 0, -1, 2, 0, -1, 0], 18), ([1, 0, -1, 2, 0, 0, -1], -18), ([1, 1, -2, 1, 0, 0, 0], -18), ([1, 1, -2, 2, 0, 0, -1], 18)]

theorem source8_checked : normalize (row ![0, -2, 2, 0, 0, 0] ![0, -2, 2, 0, 0, 0] (6, 0)) = source8 := by
  decide +kernel

theorem source8_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source8 (momentValues f) = 0 := by
  rw [← source8_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source9 : Sparse := [([0, -1, 0, -2, 0, 1, 2], 18), ([0, -1, 1, -2, 0, 0, 2], 18), ([0, 0, -1, -2, 1, 0, 2], 18), ([0, 0, 0, -3, 0, 0, 3], 36), ([0, 0, 0, -2, -1, 1, 2], 18), ([0, 0, 0, -2, 1, -1, 2], 18), ([0, 0, 0, -1, -1, 0, 2], 18), ([0, 0, 0, -1, 0, -1, 2], 18), ([0, 0, 1, -2, -1, 0, 2], -18), ([0, 0, 1, -2, 0, -1, 2], 18), ([0, 0, 1, -2, 0, 0, 1], 18), ([0, 1, -1, -2, 0, 0, 2], 18), ([0, 1, 0, -2, -1, 0, 2], 18), ([0, 1, 0, -2, 0, -1, 2], -18), ([0, 1, 0, -2, 0, 0, 1], 18), ([1, -1, 0, -2, 1, 0, 2], 18), ([1, -1, 0, -1, 0, 0, 2], -18), ([1, 0, -1, -2, 0, 1, 2], 18), ([1, 0, -1, -1, 0, 0, 2], -18), ([1, 0, 0, -2, 0, 1, 1], -18), ([1, 0, 0, -2, 1, 0, 1], -18), ([1, 0, 0, -1, -1, 0, 2], 18), ([1, 0, 0, -1, 0, -1, 2], 18), ([1, 0, 1, -2, -1, 0, 2], -18), ([1, 0, 1, -2, 0, 0, 1], 18), ([1, 1, 0, -2, 0, -1, 2], -18), ([1, 1, 0, -2, 0, 0, 1], 18)]

theorem source9_checked : normalize (row ![0, 0, -2, 0, 0, 2] ![0, 0, -2, 0, 0, 2] (6, 0)) = source9 := by
  decide +kernel

theorem source9_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source9 (momentValues f) = 0 := by
  rw [← source9_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source10 : Sparse := [([0, -1, 0, -2, 0, 2, 1], 18), ([0, -1, 0, -2, 1, 2, 0], 18), ([0, 0, -1, -2, 0, 2, 1], 18), ([0, 0, -1, -2, 1, 2, 0], -18), ([0, 0, -1, -1, 0, 2, 0], 18), ([0, 0, 0, -3, 0, 3, 0], 36), ([0, 0, 0, -2, 1, 1, 0], 18), ([0, 0, 0, -2, 1, 2, -1], 18), ([0, 0, 0, -1, 0, 2, -1], 18), ([0, 0, 1, -2, -1, 2, 0], 18), ([0, 0, 1, -2, 0, 2, -1], 18), ([0, 1, -1, -2, 0, 2, 0], 18), ([0, 1, 0, -2, -1, 2, 0], 18), ([0, 1, 0, -2, 0, 1, 0], 18), ([0, 1, 0, -2, 0, 2, -1], -18), ([1, -1, 0, -1, 0, 2, 0], -18), ([1, -1, 1, -2, 0, 2, 0], 18), ([1, 0, -1, -2, 1, 2, 0], -18), ([1, 0, -1, -1, 0, 2, 0], 18), ([1, 0, 0, -2, -1, 2, 1], 18), ([1, 0, 0, -2, 0, 1, 1], -18), ([1, 0, 0, -2, 1, 1, 0], 18), ([1, 0, 0, -1, -1, 2, 0], -18), ([1, 0, 0, -1, 0, 2, -1], 18), ([1, 0, 1, -2, 0, 1, 0], -18), ([1, 1, 0, -2, 0, 1, 0], 18), ([1, 1, 0, -2, 0, 2, -1], -18)]

theorem source10_checked : normalize (row ![0, 0, -2, 0, 2, 0] ![0, 0, -2, 0, 2, 0] (6, 0)) = source10 := by
  decide +kernel

theorem source10_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source10 (momentValues f) = 0 := by
  rw [← source10_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source11 : Sparse := [([0, -1, 0, -2, 2, 0, 1], 18), ([0, -1, 0, -2, 2, 1, 0], -18), ([0, -1, 0, -1, 2, 0, 0], 18), ([0, -1, 1, -2, 2, 0, 0], 18), ([0, 0, -1, -2, 2, 0, 1], 18), ([0, 0, -1, -2, 2, 1, 0], 18), ([0, 0, 0, -3, 3, 0, 0], 36), ([0, 0, 0, -2, 1, 1, 0], 18), ([0, 0, 0, -2, 2, 1, -1], 18), ([0, 0, 0, -1, 2, 0, -1], 18), ([0, 0, 1, -2, 1, 0, 0], 18), ([0, 0, 1, -2, 2, -1, 0], 18), ([0, 0, 1, -2, 2, 0, -1], -18), ([0, 1, 0, -2, 2, -1, 0], 18), ([0, 1, 0, -2, 2, 0, -1], 18), ([1, -1, 0, -2, 2, 1, 0], -18), ([1, -1, 0, -1, 2, 0, 0], 18), ([1, 0, -1, -1, 2, 0, 0], -18), ([1, 0, 0, -2, 1, 0, 1], -18), ([1, 0, 0, -2, 1, 1, 0], 18), ([1, 0, 0, -2, 2, -1, 1], 18), ([1, 0, 0, -1, 2, -1, 0], -18), ([1, 0, 0, -1, 2, 0, -1], 18), ([1, 0, 1, -2, 1, 0, 0], 18), ([1, 0, 1, -2, 2, 0, -1], -18), ([1, 1, -1, -2, 2, 0, 0], 18), ([1, 1, 0, -2, 1, 0, 0], -18)]

theorem source11_checked : normalize (row ![0, 0, -2, 2, 0, 0] ![0, 0, -2, 2, 0, 0] (6, 0)) = source11 := by
  decide +kernel

theorem source11_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source11 (momentValues f) = 0 := by
  rw [← source11_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source12 : Sparse := [([0, -1, 0, 0, -2, 1, 2], 18), ([0, -1, 1, 0, -2, 0, 2], 18), ([0, 0, -1, 0, -2, 1, 2], 18), ([0, 0, -1, 0, -1, 0, 2], 18), ([0, 0, -1, 1, -2, 0, 2], 18), ([0, 0, 0, -1, -2, 1, 2], -18), ([0, 0, 0, -1, -1, 0, 2], 18), ([0, 0, 0, 0, -3, 0, 3], 36), ([0, 0, 0, 0, -2, 1, 1], 18), ([0, 0, 0, 1, -2, -1, 2], 18), ([0, 0, 1, -1, -2, 0, 2], 18), ([0, 1, -1, 0, -2, 0, 2], -18), ([0, 1, 0, -1, -2, 0, 2], 18), ([0, 1, 0, 0, -2, -1, 2], 18), ([0, 1, 0, 0, -2, 0, 1], 18), ([1, -1, 0, 0, -1, 0, 2], -18), ([1, -1, 0, 1, -2, 0, 2], 18), ([1, 0, -1, 0, -1, 0, 2], 18), ([1, 0, 0, -1, -2, 1, 2], -18), ([1, 0, 0, -1, -1, 0, 2], 18), ([1, 0, 0, 0, -2, 1, 1], 18), ([1, 0, 0, 0, -1, -1, 2], -18), ([1, 0, 0, 1, -2, 0, 1], -18), ([1, 0, 1, 0, -2, -1, 2], 18), ([1, 0, 1, 0, -2, 0, 1], -18), ([1, 1, -1, 0, -2, 0, 2], -18), ([1, 1, 0, 0, -2, 0, 1], 18)]

theorem source12_checked : normalize (row ![0, 0, 0, -2, 0, 2] ![0, 0, 0, -2, 0, 2] (6, 0)) = source12 := by
  decide +kernel

theorem source12_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source12 (momentValues f) = 0 := by
  rw [← source12_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source13 : Sparse := [([0, -1, 0, 0, -2, 2, 1], -18), ([0, -1, 0, 0, -1, 2, 0], 18), ([0, -1, 0, 1, -2, 2, 0], 18), ([0, -1, 1, 0, -2, 2, 0], 18), ([0, 0, -1, 0, -2, 2, 1], 18), ([0, 0, -1, 0, -1, 2, 0], 18), ([0, 0, -1, 1, -2, 2, 0], -18), ([0, 0, 0, -1, -2, 2, 1], 18), ([0, 0, 0, 0, -3, 3, 0], 36), ([0, 0, 0, 0, -2, 1, 1], 18), ([0, 0, 0, 1, -2, 1, 0], 18), ([0, 0, 0, 1, -2, 2, -1], 18), ([0, 0, 1, -1, -2, 2, 0], 18), ([0, 1, -1, 0, -2, 2, 0], 18), ([0, 1, 0, 0, -2, 2, -1], 18), ([1, -1, 0, 0, -2, 2, 1], -18), ([1, -1, 0, 0, -1, 2, 0], 18), ([1, 0, -1, 0, -1, 2, 0], 18), ([1, 0, -1, 1, -2, 2, 0], -18), ([1, 0, 0, -1, -1, 2, 0], -18), ([1, 0, 0, 0, -2, 1, 1], 18), ([1, 0, 0, 0, -1, 2, -1], -18), ([1, 0, 0, 1, -2, 1, 0], 18), ([1, 0, 1, 0, -2, 1, 0], -18), ([1, 0, 1, 0, -2, 2, -1], 18), ([1, 1, 0, -1, -2, 2, 0], 18), ([1, 1, 0, 0, -2, 1, 0], -18)]

theorem source13_checked : normalize (row ![0, 0, 0, -2, 2, 0] ![0, 0, 0, -2, 2, 0] (6, 0)) = source13 := by
  decide +kernel

theorem source13_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source13 (momentValues f) = 0 := by
  rw [← source13_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source14 : Sparse := [([0, -1, 0, 0, 0, -1, 2], 18), ([0, -1, 0, 0, 1, -2, 2], 18), ([0, -1, 0, 1, 0, -2, 2], 18), ([0, -1, 1, 0, 0, -2, 2], -18), ([0, 0, -1, 0, 1, -2, 2], 18), ([0, 0, 0, -1, 0, -1, 2], 18), ([0, 0, 0, -1, 1, -2, 2], -18), ([0, 0, 0, 0, 0, -3, 3], 36), ([0, 0, 0, 0, 1, -2, 1], 18), ([0, 0, 0, 1, -1, -2, 2], 18), ([0, 0, 1, -1, 0, -2, 2], 18), ([0, 0, 1, 0, -1, -2, 2], 18), ([0, 0, 1, 0, 0, -2, 1], 18), ([0, 1, -1, 0, 0, -2, 2], 18), ([0, 1, 0, -1, 0, -2, 2], 18), ([1, -1, 0, 0, 0, -1, 2], 18), ([1, -1, 1, 0, 0, -2, 2], -18), ([1, 0, -1, 0, 0, -1, 2], -18), ([1, 0, -1, 1, 0, -2, 2], 18), ([1, 0, 0, -1, 0, -1, 2], 18), ([1, 0, 0, -1, 1, -2, 2], -18), ([1, 0, 0, 0, -1, -1, 2], -18), ([1, 0, 0, 0, 1, -2, 1], 18), ([1, 0, 0, 1, 0, -2, 1], -18), ([1, 0, 1, 0, 0, -2, 1], 18), ([1, 1, 0, 0, -1, -2, 2], 18), ([1, 1, 0, 0, 0, -2, 1], -18)]

theorem source14_checked : normalize (row ![0, 0, 0, 0, -2, 2] ![0, 0, 0, 0, -2, 2] (6, 0)) = source14 := by
  decide +kernel

theorem source14_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source14 (momentValues f) = 0 := by
  rw [← source14_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source15 : Sparse := [([0, -1, 0, 0, 0, 2, -1], 18), ([0, -1, 0, 0, 1, 2, -2], -18), ([0, -1, 0, 1, 0, 2, -2], 18), ([0, -1, 1, 0, 0, 2, -2], 18), ([0, 0, -1, 0, 1, 2, -2], 18), ([0, 0, -1, 1, 0, 2, -2], 18), ([0, 0, 0, -1, 0, 2, -1], 18), ([0, 0, 0, -1, 1, 2, -2], 18), ([0, 0, 0, 0, 0, 3, -3], 36), ([0, 0, 0, 0, 1, 1, -2], 18), ([0, 0, 1, -1, 0, 2, -2], -18), ([0, 0, 1, 0, -1, 2, -2], 18), ([0, 0, 1, 0, 0, 1, -2], 18), ([0, 1, 0, -1, 0, 2, -2], 18), ([0, 1, 0, 0, -1, 2, -2], 18), ([1, -1, 0, 0, 0, 2, -1], 18), ([1, -1, 0, 0, 1, 2, -2], -18), ([1, 0, -1, 0, 0, 2, -1], -18), ([1, 0, 0, -1, 0, 2, -1], 18), ([1, 0, 0, 0, -1, 2, -1], -18), ([1, 0, 0, 0, 1, 1, -2], 18), ([1, 0, 0, 1, -1, 2, -2], 18), ([1, 0, 0, 1, 0, 1, -2], -18), ([1, 0, 1, -1, 0, 2, -2], -18), ([1, 0, 1, 0, 0, 1, -2], 18), ([1, 1, -1, 0, 0, 2, -2], 18), ([1, 1, 0, 0, 0, 1, -2], -18)]

theorem source15_checked : normalize (row ![0, 0, 0, 0, 2, -2] ![0, 0, 0, 0, 2, -2] (6, 0)) = source15 := by
  decide +kernel

theorem source15_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source15 (momentValues f) = 0 := by
  rw [← source15_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
