import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source48 : Sparse := [([0, -2, 2, -1, 0, 0, 1], -36), ([0, -1, 0, -1, 1, 0, 1], -36), ([0, -1, 1, -2, 0, 0, 2], -36), ([0, -1, 1, -1, 0, 1, 0], -36), ([0, -1, 1, -1, 1, -1, 1], -36), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, 0, 0, -1, 1], -36), ([0, -1, 2, -2, 0, 0, 1], 36), ([0, -1, 2, -1, 0, 0, 0], -36), ([0, 0, 1, -2, 0, 0, 1], -36), ([0, 0, 1, -1, -1, 0, 1], -36), ([0, 0, 1, -1, 0, -1, 1], 36), ([1, -2, 1, -1, 0, 0, 2], -36), ([1, -2, 1, 0, 0, 0, 1], 36), ([1, -1, 0, -1, 0, 0, 2], 36), ([1, -1, 0, -1, 0, 1, 1], -36), ([1, -1, 1, -1, -1, 1, 1], 36), ([1, -1, 1, -1, 1, -1, 1], -36), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, 0, -1, 0, 1], -36), ([1, -1, 2, -2, 0, 0, 1], 36), ([1, -1, 2, -1, 0, 0, 0], -36), ([1, 0, 1, -2, 0, 0, 1], -36), ([1, 0, 1, -1, 0, -1, 1], 36)]

theorem source48_checked : normalize (row ![-1, 1, -1, 0, 0, 1] ![-1, 1, -1, 0, 0, 1] (-12, 0)) = source48 := by
  decide +kernel

theorem source48_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source48 (momentValues f) = 0 := by
  rw [← source48_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source49 : Sparse := [([0, -2, 1, -1, 0, 2, 0], -36), ([0, -2, 1, 0, 0, 1, 0], -36), ([0, -2, 2, -1, 0, 1, 0], 36), ([0, -1, 0, -1, 1, 1, 0], -36), ([0, -1, 1, -1, 0, 0, 1], -36), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, -1, 1, 1, -1], -36), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, -1, 2, -2, 0, 1, 0], -36), ([0, -1, 2, -1, 0, 0, 0], -36), ([0, 0, 1, -1, 0, 1, -1], -36), ([1, -2, 1, 0, 0, 1, 0], -36), ([1, -2, 2, -1, 0, 1, 0], 36), ([1, -1, 0, -1, 0, 1, 1], -36), ([1, -1, 0, -1, 0, 2, 0], 36), ([1, -1, 1, -2, 0, 2, 0], -36), ([1, -1, 1, -1, -1, 1, 1], 36), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, -1, 1, 1, -1], -36), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, -1, 2, -1, 0, 0, 0], -36), ([1, 0, 1, -2, 0, 1, 0], 36), ([1, 0, 1, -1, -1, 1, 0], -36)]

theorem source49_checked : normalize (row ![-1, 1, -1, 0, 1, 0] ![-1, 1, -1, 0, 1, 0] (-12, 0)) = source49 := by
  decide +kernel

theorem source49_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source49 (momentValues f) = 0 := by
  rw [← source49_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source50 : Sparse := [([0, -2, 1, -1, 2, 0, 0], -36), ([0, -2, 1, 0, 1, 0, 0], -36), ([0, -2, 2, -1, 1, 0, 0], -36), ([0, -1, 0, -1, 1, 0, 1], -36), ([0, -1, 0, -1, 1, 1, 0], -36), ([0, -1, 0, -1, 2, 0, 0], -36), ([0, -1, 1, -2, 2, 0, 0], -36), ([0, -1, 1, -1, 0, 0, 1], -36), ([0, -1, 1, -1, 0, 1, 0], -36), ([0, -1, 1, -1, 1, -1, 1], -36), ([0, -1, 1, -1, 1, 1, -1], -36), ([0, -1, 1, 0, 1, -1, 0], -36), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, -1, 2, -2, 1, 0, 0], -36), ([0, -1, 2, -1, 0, 0, 0], -36), ([0, 0, 1, -2, 1, 0, 0], -36), ([0, 0, 1, -1, 1, -1, 0], -36), ([0, 0, 1, -1, 1, 0, -1], -36), ([1, -2, 1, 0, 1, 0, 0], -36), ([1, -1, 0, -1, 2, 0, 0], -36), ([1, -1, 1, -1, 1, -1, 1], -36), ([1, -1, 1, -1, 1, 1, -1], -36), ([1, -1, 2, -1, 0, 0, 0], -36), ([1, 0, 1, -2, 1, 0, 0], -36)]

theorem source50_checked : normalize (row ![-1, 1, -1, 1, 0, 0] ![-1, 1, -1, 1, 0, 0] (-12, 0)) = source50 := by
  decide +kernel

theorem source50_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source50 (momentValues f) = 0 := by
  rw [← source50_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source51 : Sparse := [([0, -2, 1, 0, -1, 0, 2], -36), ([0, -2, 2, 0, -1, 0, 1], -36), ([0, -1, 0, 0, -1, 1, 1], -36), ([0, -1, 0, 1, -1, 0, 1], -36), ([0, -1, 1, -1, 0, 0, 1], -36), ([0, -1, 1, 0, -2, 0, 2], -36), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, -1, 1, 0, 0, -1, 1], -36), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 2, 0, -2, 0, 1], -36), ([0, 0, 1, -1, -1, 0, 1], -36), ([0, 0, 1, 0, -1, -1, 1], -36), ([1, -2, 1, 0, 0, 0, 1], 36), ([1, -1, 0, 0, -1, 0, 2], 36), ([1, -1, 1, -1, -1, 1, 1], 36), ([1, -1, 1, 1, -1, -1, 1], 36), ([1, -1, 2, 0, -1, 0, 0], 36), ([1, 0, 1, 0, -2, 0, 1], 36)]

theorem source51_checked : normalize (row ![-1, 1, 0, -1, 0, 1] ![-1, 1, 0, -1, 0, 1] (-12, 0)) = source51 := by
  decide +kernel

theorem source51_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source51 (momentValues f) = 0 := by
  rw [← source51_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source52 : Sparse := [([0, -2, 1, 0, -1, 2, 0], 36), ([0, -2, 1, 0, 0, 1, 0], -36), ([0, -2, 2, 0, -1, 1, 0], -36), ([0, -1, 0, 0, -1, 1, 1], -36), ([0, -1, 0, 0, -1, 2, 0], -36), ([0, -1, 0, 1, -1, 1, 0], 36), ([0, -1, 1, -1, 0, 1, 0], -36), ([0, -1, 1, 0, -2, 2, 0], -36), ([0, -1, 1, 0, 0, 1, -1], 36), ([0, -1, 1, 1, -1, 0, 0], -36), ([0, -1, 1, 1, -1, 1, -1], -36), ([0, 0, 1, 0, -1, 1, -1], -36), ([1, -2, 1, 0, -1, 2, 0], 36), ([1, -2, 1, 0, 0, 1, 0], -36), ([1, -1, 0, 0, -1, 2, 0], -36), ([1, -1, 0, 1, -1, 1, 0], 36), ([1, -1, 1, -1, -1, 1, 1], 36), ([1, -1, 1, 0, -1, 0, 1], -36), ([1, -1, 1, 0, 0, 1, -1], 36), ([1, -1, 1, 1, -1, 1, -1], -36), ([1, -1, 2, 0, -2, 1, 0], -36), ([1, -1, 2, 0, -1, 0, 0], 36), ([1, 0, 1, -1, -1, 1, 0], -36), ([1, 0, 1, 0, -2, 1, 0], 36)]

theorem source52_checked : normalize (row ![-1, 1, 0, -1, 1, 0] ![-1, 1, 0, -1, 1, 0] (-12, 0)) = source52 := by
  decide +kernel

theorem source52_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source52 (momentValues f) = 0 := by
  rw [← source52_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source53 : Sparse := [([0, -2, 1, 0, 0, -1, 2], -36), ([0, -1, 0, 0, 0, -1, 2], -36), ([0, -1, 0, 0, 1, -1, 1], 36), ([0, -1, 0, 1, 0, -1, 1], -36), ([0, -1, 1, -1, 0, 0, 1], -36), ([0, -1, 1, -1, 1, -1, 1], -36), ([0, -1, 1, 0, 0, -2, 2], 36), ([0, -1, 1, 0, 1, -1, 0], -36), ([0, -1, 2, 0, 0, -2, 1], -36), ([0, 0, 1, -1, 0, -1, 1], 36), ([0, 0, 1, 0, -1, -1, 1], -36), ([0, 0, 1, 0, 0, -2, 1], -36), ([1, -2, 1, 0, 0, 0, 1], 36), ([1, -2, 2, 0, 0, -1, 1], -36), ([1, -1, 0, 0, 0, -1, 2], -36), ([1, -1, 0, 0, 1, -1, 1], 36), ([1, -1, 1, -1, 1, -1, 1], -36), ([1, -1, 1, 0, -1, 0, 1], -36), ([1, -1, 1, 0, 0, -2, 2], 36), ([1, -1, 1, 1, -1, -1, 1], 36), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 2, 0, 0, -1, 0], 36), ([1, 0, 1, -1, 0, -1, 1], 36), ([1, 0, 1, 0, 0, -2, 1], -36)]

theorem source53_checked : normalize (row ![-1, 1, 0, 0, -1, 1] ![-1, 1, 0, 0, -1, 1] (-12, 0)) = source53 := by
  decide +kernel

theorem source53_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source53 (momentValues f) = 0 := by
  rw [← source53_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source54 : Sparse := [([0, -2, 1, 0, 0, 1, 0], -36), ([0, -2, 1, 0, 0, 2, -1], -36), ([0, -2, 2, 0, 0, 1, -1], -36), ([0, -1, 0, 0, 0, 2, -1], -36), ([0, -1, 0, 0, 1, 1, -1], -36), ([0, -1, 0, 1, 0, 1, -1], -36), ([0, -1, 1, -1, 0, 1, 0], -36), ([0, -1, 1, -1, 1, 1, -1], -36), ([0, -1, 1, 0, -1, 1, 0], -36), ([0, -1, 1, 0, 0, 2, -2], -36), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, -1, 1, 1, -1, 1, -1], -36), ([0, -1, 1, 1, 0, 0, -1], -36), ([0, -1, 2, 0, 0, 0, -1], -36), ([0, -1, 2, 0, 0, 1, -2], -36), ([0, 0, 1, -1, 0, 1, -1], -36), ([0, 0, 1, 0, -1, 1, -1], -36), ([0, 0, 1, 0, 0, 1, -2], -36), ([1, -2, 1, 0, 0, 1, 0], -36), ([1, -1, 0, 0, 0, 2, -1], -36), ([1, -1, 1, -1, 1, 1, -1], -36), ([1, -1, 1, 1, -1, 1, -1], -36), ([1, -1, 2, 0, 0, 0, -1], -36), ([1, 0, 1, 0, 0, 1, -2], -36)]

theorem source54_checked : normalize (row ![-1, 1, 0, 0, 1, -1] ![-1, 1, 0, 0, 1, -1] (-12, 0)) = source54 := by
  decide +kernel

theorem source54_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source54 (momentValues f) = 0 := by
  rw [← source54_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source55 : Sparse := [([0, -2, 1, 0, 1, 0, 0], -36), ([0, -2, 1, 0, 2, -1, 0], 36), ([0, -2, 2, 0, 1, -1, 0], -36), ([0, -1, 0, 0, 1, -1, 1], 36), ([0, -1, 0, 0, 2, -1, 0], -36), ([0, -1, 0, 1, 1, -1, 0], -36), ([0, -1, 1, -1, 1, -1, 1], -36), ([0, -1, 1, -1, 1, 0, 0], 36), ([0, -1, 1, 0, 0, -1, 1], -36), ([0, -1, 1, 0, 1, 0, -1], -36), ([0, -1, 1, 0, 2, -2, 0], -36), ([0, 0, 1, -1, 1, -1, 0], -36), ([1, -2, 1, 0, 1, 0, 0], -36), ([1, -2, 1, 0, 2, -1, 0], 36), ([1, -1, 0, 0, 1, -1, 1], 36), ([1, -1, 0, 0, 2, -1, 0], -36), ([1, -1, 1, -1, 1, -1, 1], -36), ([1, -1, 1, -1, 1, 0, 0], 36), ([1, -1, 1, 1, 0, -1, 0], -36), ([1, -1, 1, 1, 1, -1, -1], 36), ([1, -1, 2, 0, 0, -1, 0], 36), ([1, -1, 2, 0, 1, -2, 0], -36), ([1, 0, 1, 0, 1, -2, 0], 36), ([1, 0, 1, 0, 1, -1, -1], -36)]

theorem source55_checked : normalize (row ![-1, 1, 0, 1, -1, 0] ![-1, 1, 0, 1, -1, 0] (-12, 0)) = source55 := by
  decide +kernel

theorem source55_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source55 (momentValues f) = 0 := by
  rw [← source55_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
