import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source104 : Sparse := [([0, 0, 0, -1, 0, -1, 2], -36), ([0, 0, 0, -1, 1, -1, 1], -36), ([0, 0, 1, -1, 0, -1, 1], 36), ([0, 1, -1, -1, 0, 0, 1], -36), ([0, 1, 0, -2, 0, -1, 2], 36), ([0, 1, 0, -2, 0, 0, 1], -36), ([0, 1, 0, -1, -1, 0, 1], 36), ([0, 1, 0, -1, 0, -2, 2], -36), ([0, 1, 0, 0, -1, -1, 1], -36), ([0, 1, 1, -1, -1, -1, 1], -36), ([0, 1, 1, -1, 0, -1, 0], -36), ([0, 2, 0, -2, 0, -1, 1], -36), ([1, 0, 0, -1, 0, -1, 2], -36), ([1, 0, 1, -1, 0, -1, 1], 36), ([1, 1, -1, -1, 1, -1, 1], 36), ([1, 1, -1, 0, 0, -1, 1], -36), ([1, 1, 0, -2, 0, -1, 2], 36), ([1, 1, 0, -2, 0, 0, 1], -36), ([1, 1, 0, -1, -1, 0, 1], 36), ([1, 1, 0, -1, 1, -1, 0], -36), ([1, 1, 0, 0, 0, -2, 1], 36), ([1, 1, 1, -1, -1, -1, 1], -36), ([1, 2, 0, -1, 0, -2, 1], -36), ([1, 2, 0, -1, 0, -1, 0], 36)]

theorem source104_checked : normalize (row ![1, 0, -1, 0, -1, 1] ![1, 0, -1, 0, -1, 1] (-12, 0)) = source104 := by
  decide +kernel

theorem source104_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source104 (momentValues f) = 0 := by
  rw [← source104_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source105 : Sparse := [([0, 0, 0, -1, 0, 2, -1], -36), ([0, 0, 0, -1, 1, 1, -1], 36), ([0, 0, 1, -1, 0, 1, -1], -36), ([0, 1, -1, -1, 0, 1, 0], 36), ([0, 1, -1, -1, 1, 1, -1], -36), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, 0, -2, 0, 1, 0], -36), ([0, 1, 0, -2, 0, 2, -1], 36), ([0, 1, 0, -1, -1, 1, 0], -36), ([0, 1, 0, -1, 0, 2, -2], -36), ([0, 1, 0, -1, 1, 0, -1], -36), ([0, 2, 0, -2, 0, 1, -1], -36), ([1, 0, 0, -1, 0, 2, -1], -36), ([1, 0, 0, -1, 1, 1, -1], 36), ([1, 1, -1, -1, 0, 1, 0], 36), ([1, 1, -1, -1, 1, 1, -1], -36), ([1, 1, 0, -2, 0, 1, 0], -36), ([1, 1, 0, -2, 0, 2, -1], 36), ([1, 1, 0, 0, -1, 1, -1], -36), ([1, 1, 0, 0, 0, 1, -2], 36), ([1, 1, 1, -1, -1, 1, -1], 36), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 2, 0, -1, 0, 0, -1], 36), ([1, 2, 0, -1, 0, 1, -2], -36)]

theorem source105_checked : normalize (row ![1, 0, -1, 0, 1, -1] ![1, 0, -1, 0, 1, -1] (-12, 0)) = source105 := by
  decide +kernel

theorem source105_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source105 (momentValues f) = 0 := by
  rw [← source105_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source106 : Sparse := [([0, 0, 0, -1, 1, -1, 1], -36), ([0, 0, 1, -1, 1, -1, 0], -36), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, 0, 1, -1, 0], -36), ([0, 1, 0, -2, 2, -1, 0], -36), ([0, 1, 0, -1, 0, -1, 1], -36), ([0, 1, 0, -1, 1, 0, -1], -36), ([0, 1, 0, -1, 2, -2, 0], -36), ([0, 1, 0, 0, 1, -1, -1], -36), ([0, 1, 1, -1, 0, -1, 0], -36), ([0, 2, 0, -2, 1, -1, 0], -36), ([0, 2, 0, -1, 1, -2, 0], -36), ([1, 0, 0, -1, 2, -1, 0], 36), ([1, 1, -1, -1, 1, -1, 1], 36), ([1, 1, 0, -2, 1, 0, 0], 36), ([1, 1, 0, 0, 1, -2, 0], 36), ([1, 1, 1, -1, 1, -1, -1], 36), ([1, 2, 0, -1, 0, -1, 0], 36)]

theorem source106_checked : normalize (row ![1, 0, -1, 1, -1, 0] ![1, 0, -1, 1, -1, 0] (-12, 0)) = source106 := by
  decide +kernel

theorem source106_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source106 (momentValues f) = 0 := by
  rw [← source106_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source107 : Sparse := [([0, 0, 0, -1, 1, 1, -1], 36), ([0, 0, 0, -1, 2, 0, -1], -36), ([0, 0, 1, -1, 1, 0, -1], -36), ([0, 1, -1, -1, 1, 0, 0], -36), ([0, 1, -1, -1, 1, 1, -1], -36), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, 0, -2, 2, 0, -1], -36), ([0, 1, 0, -1, 0, 1, -1], -36), ([0, 1, 0, -1, 2, 0, -2], 36), ([0, 1, 0, 0, 1, -1, -1], -36), ([0, 1, 0, 0, 1, 0, -2], -36), ([0, 2, 0, -1, 1, 0, -2], -36), ([1, 0, 0, -1, 1, 1, -1], 36), ([1, 0, 0, -1, 2, 0, -1], -36), ([1, 1, -1, -1, 1, 1, -1], -36), ([1, 1, -1, 0, 1, 0, -1], 36), ([1, 1, 0, -2, 1, 0, 0], 36), ([1, 1, 0, -1, 1, -1, 0], -36), ([1, 1, 0, -1, 2, 0, -2], 36), ([1, 1, 0, 0, 1, 0, -2], -36), ([1, 1, 1, -1, 0, 0, -1], -36), ([1, 1, 1, -1, 1, -1, -1], 36), ([1, 2, 0, -2, 1, 0, -1], -36), ([1, 2, 0, -1, 0, 0, -1], 36)]

theorem source107_checked : normalize (row ![1, 0, -1, 1, 0, -1] ![1, 0, -1, 1, 0, -1] (-12, 0)) = source107 := by
  decide +kernel

theorem source107_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source107 (momentValues f) = 0 := by
  rw [← source107_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source108 : Sparse := [([0, 0, 1, 0, -1, -1, 1], -36), ([0, 1, -1, 0, -1, 0, 1], -36), ([0, 1, 0, -1, -1, 0, 1], 36), ([0, 1, 0, -1, 0, -1, 1], -36), ([0, 1, 0, 0, -2, -1, 2], -36), ([0, 1, 0, 0, -2, 0, 1], -36), ([0, 1, 0, 1, -1, -1, 0], -36), ([0, 1, 1, -1, -1, -1, 1], -36), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 2, 0, 0, -2, -1, 1], 36), ([0, 2, 0, 0, -1, -2, 1], -36), ([0, 2, 0, 0, -1, -1, 0], -36), ([1, 0, 0, 0, -1, -1, 2], 36), ([1, 0, 0, 1, -1, -1, 1], -36), ([1, 1, -1, 0, 0, -1, 1], -36), ([1, 1, -1, 1, -1, -1, 1], 36), ([1, 1, 0, -1, -1, 0, 1], 36), ([1, 1, 0, 0, -2, 0, 1], -36), ([1, 1, 0, 0, -1, -2, 2], -36), ([1, 1, 0, 0, 0, -2, 1], 36), ([1, 1, 1, -1, -1, -1, 1], -36), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 2, 0, 0, -2, -1, 1], 36), ([1, 2, 0, 0, -1, -1, 0], -36)]

theorem source108_checked : normalize (row ![1, 0, 0, -1, -1, 1] ![1, 0, 0, -1, -1, 1] (-12, 0)) = source108 := by
  decide +kernel

theorem source108_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source108 (momentValues f) = 0 := by
  rw [← source108_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source109 : Sparse := [([0, 0, 0, 1, -1, 1, -1], -36), ([0, 0, 1, 0, -1, 1, -1], -36), ([0, 1, -1, 0, -1, 1, 0], -36), ([0, 1, -1, 0, 0, 1, -1], -36), ([0, 1, 0, -1, -1, 1, 0], -36), ([0, 1, 0, -1, 0, 1, -1], -36), ([0, 1, 0, 0, -2, 2, -1], -36), ([0, 1, 0, 0, -1, 2, -2], -36), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 1, 1, 0, -1, 0, -1], -36), ([0, 2, 0, 0, -2, 1, -1], -36), ([0, 2, 0, 0, -1, 1, -2], -36), ([1, 0, 0, 0, -1, 2, -1], 36), ([1, 1, -1, 1, -1, 1, -1], 36), ([1, 1, 0, 0, -2, 1, 0], 36), ([1, 1, 0, 0, 0, 1, -2], 36), ([1, 1, 1, -1, -1, 1, -1], 36), ([1, 2, 0, 0, -1, 0, -1], 36)]

theorem source109_checked : normalize (row ![1, 0, 0, -1, 1, -1] ![1, 0, 0, -1, 1, -1] (-12, 0)) = source109 := by
  decide +kernel

theorem source109_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source109 (momentValues f) = 0 := by
  rw [← source109_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source110 : Sparse := [([0, 0, 0, 1, 1, -1, -1], -36), ([0, 1, -1, 0, 1, -1, 0], -36), ([0, 1, -1, 0, 1, 0, -1], 36), ([0, 1, -1, 1, 1, -1, -1], -36), ([0, 1, 0, -1, 1, 0, -1], -36), ([0, 1, 0, 0, 1, 0, -2], -36), ([0, 1, 0, 0, 2, -1, -2], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 1, 1, 0, 0, -1, -1], -36), ([0, 2, 0, 0, 0, -1, -1], -36), ([0, 2, 0, 0, 1, -2, -1], -36), ([0, 2, 0, 0, 1, -1, -2], 36), ([1, 0, 0, 0, 2, -1, -1], 36), ([1, 0, 1, 0, 1, -1, -1], -36), ([1, 1, -1, 0, 1, 0, -1], 36), ([1, 1, -1, 1, 1, -1, -1], -36), ([1, 1, 0, -1, 1, -1, 0], -36), ([1, 1, 0, 0, 1, -2, 0], 36), ([1, 1, 0, 0, 1, 0, -2], -36), ([1, 1, 0, 0, 2, -2, -1], -36), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 1, 1, -1, 1, -1, -1], 36), ([1, 2, 0, 0, 0, -1, -1], -36), ([1, 2, 0, 0, 1, -1, -2], 36)]

theorem source110_checked : normalize (row ![1, 0, 0, 1, -1, -1] ![1, 0, 0, 1, -1, -1] (-12, 0)) = source110 := by
  decide +kernel

theorem source110_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source110 (momentValues f) = 0 := by
  rw [← source110_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source111 : Sparse := [([0, 0, 1, 1, -1, -1, 0], -36), ([0, 1, -1, 1, 0, -1, 0], -36), ([0, 1, 0, 0, -1, -1, 1], -36), ([0, 1, 0, 1, -1, 0, -1], -36), ([0, 1, 0, 1, 0, -2, 0], -36), ([0, 1, 0, 1, 0, -1, -1], 36), ([0, 1, 0, 2, -1, -2, 0], -36), ([0, 1, 1, 0, -1, -1, 0], 36), ([0, 1, 1, 1, -1, -1, -1], -36), ([0, 2, 0, 0, -1, -1, 0], -36), ([0, 2, 0, 1, -2, -1, 0], -36), ([0, 2, 0, 1, -1, -2, 0], 36), ([1, 0, 0, 1, -1, -1, 1], -36), ([1, 0, 0, 2, -1, -1, 0], 36), ([1, 1, -1, 1, -1, -1, 1], 36), ([1, 1, -1, 1, -1, 0, 0], -36), ([1, 1, 0, 1, -2, 0, 0], 36), ([1, 1, 0, 1, 0, -2, 0], -36), ([1, 1, 0, 1, 0, -1, -1], 36), ([1, 1, 0, 2, -2, -1, 0], -36), ([1, 1, 1, 0, -1, -1, 0], 36), ([1, 1, 1, 1, -1, -1, -1], -36), ([1, 2, 0, 0, -1, -1, 0], -36), ([1, 2, 0, 1, -1, -2, 0], 36)]

theorem source111_checked : normalize (row ![1, 0, 1, -1, -1, 0] ![1, 0, 1, -1, -1, 0] (-12, 0)) = source111 := by
  decide +kernel

theorem source111_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source111 (momentValues f) = 0 := by
  rw [← source111_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
