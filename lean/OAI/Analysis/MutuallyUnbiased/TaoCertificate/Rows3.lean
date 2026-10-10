import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source24 : Sparse := [([0, -1, 2, 0, 0, 0, -1], 18), ([0, -1, 2, 0, 0, 1, -2], 18), ([0, -1, 2, 0, 1, 0, -2], 18), ([0, -1, 2, 1, 0, 0, -2], -18), ([0, 0, 1, 0, 0, 1, -2], 18), ([0, 0, 1, 1, 0, 0, -2], 18), ([0, 0, 2, -1, 0, 1, -2], 18), ([0, 0, 2, 0, -1, 0, -1], 18), ([0, 0, 2, 0, -1, 1, -2], -18), ([0, 0, 2, 0, 1, -1, -2], 18), ([0, 0, 2, 1, -1, 0, -2], 18), ([0, 0, 2, 1, 0, -1, -2], 18), ([0, 0, 3, 0, 0, 0, -3], 36), ([0, 1, 2, -1, 0, 0, -2], 18), ([0, 1, 2, 0, -1, 0, -2], 18), ([1, -1, 2, 0, 0, 0, -1], 18), ([1, -1, 2, 1, 0, 0, -2], -18), ([1, 0, 1, 0, 0, 1, -2], 18), ([1, 0, 1, 0, 1, 0, -2], -18), ([1, 0, 1, 1, 0, 0, -2], 18), ([1, 0, 2, -1, 0, 0, -1], -18), ([1, 0, 2, -1, 1, 0, -2], 18), ([1, 0, 2, 0, -1, 0, -1], 18), ([1, 0, 2, 0, -1, 1, -2], -18), ([1, 0, 2, 0, 0, -1, -1], -18), ([1, 1, 1, 0, 0, 0, -2], -18), ([1, 1, 2, 0, 0, -1, -2], 18)]

theorem source24_checked : normalize (row ![0, 2, 0, 0, 0, -2] ![0, 2, 0, 0, 0, -2] (6, 0)) = source24 := by
  decide +kernel

theorem source24_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source24 (momentValues f) = 0 := by
  rw [← source24_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source25 : Sparse := [([0, 1, -2, 0, 0, 1, 0], 18), ([0, 1, -2, 0, 1, 0, 0], 18), ([0, 2, -2, -1, 0, 0, 1], 18), ([0, 2, -2, -1, 0, 1, 0], 18), ([0, 2, -2, -1, 1, 0, 0], -18), ([0, 2, -2, 0, -1, 1, 0], 18), ([0, 2, -2, 0, 0, -1, 1], 18), ([0, 2, -2, 0, 0, 1, -1], -18), ([0, 2, -2, 0, 1, -1, 0], 18), ([0, 2, -2, 0, 1, 0, -1], 18), ([0, 2, -2, 1, -1, 0, 0], 18), ([0, 2, -2, 1, 0, 0, -1], 18), ([0, 2, -1, -1, 0, 0, 0], 18), ([0, 2, -1, 0, 0, 0, -1], 18), ([0, 3, -3, 0, 0, 0, 0], 36), ([1, 1, -2, 0, 0, 0, 1], -18), ([1, 1, -2, 0, 0, 1, 0], 18), ([1, 1, -2, 0, 1, 0, 0], 18), ([1, 1, -2, 1, 0, 0, 0], -18), ([1, 2, -2, -1, 1, 0, 0], -18), ([1, 2, -2, 0, -1, 0, 1], 18), ([1, 2, -2, 0, 0, 1, -1], -18), ([1, 2, -2, 1, 0, -1, 0], 18), ([1, 2, -1, -1, 0, 0, 0], 18), ([1, 2, -1, 0, -1, 0, 0], -18), ([1, 2, -1, 0, 0, -1, 0], -18), ([1, 2, -1, 0, 0, 0, -1], 18)]

theorem source25_checked : normalize (row ![2, -2, 0, 0, 0, 0] ![2, -2, 0, 0, 0, 0] (6, 0)) = source25 := by
  decide +kernel

theorem source25_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source25 (momentValues f) = 0 := by
  rw [← source25_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source26 : Sparse := [([0, 1, 0, -2, 0, 0, 1], 18), ([0, 1, 0, -2, 0, 1, 0], 18), ([0, 2, -1, -2, 0, 0, 1], -18), ([0, 2, -1, -2, 0, 1, 0], 18), ([0, 2, -1, -2, 1, 0, 0], 18), ([0, 2, -1, -1, 0, 0, 0], 18), ([0, 2, 0, -2, -1, 0, 1], 18), ([0, 2, 0, -2, -1, 1, 0], -18), ([0, 2, 0, -2, 0, -1, 1], 18), ([0, 2, 0, -2, 0, 1, -1], 18), ([0, 2, 0, -2, 1, -1, 0], 18), ([0, 2, 0, -1, -1, 0, 0], 18), ([0, 2, 1, -2, -1, 0, 0], 18), ([0, 2, 1, -2, 0, 0, -1], 18), ([0, 3, 0, -3, 0, 0, 0], 36), ([1, 1, 0, -2, 0, 0, 1], 18), ([1, 1, 0, -2, 0, 1, 0], 18), ([1, 1, 0, -2, 1, 0, 0], -18), ([1, 1, 1, -2, 0, 0, 0], -18), ([1, 2, -1, -2, 0, 0, 1], -18), ([1, 2, -1, -1, 0, 0, 0], 18), ([1, 2, 0, -2, -1, 1, 0], -18), ([1, 2, 0, -2, 1, 0, -1], 18), ([1, 2, 0, -1, -1, 0, 0], 18), ([1, 2, 0, -1, 0, -1, 0], -18), ([1, 2, 0, -1, 0, 0, -1], -18), ([1, 2, 1, -2, 0, -1, 0], 18)]

theorem source26_checked : normalize (row ![2, 0, -2, 0, 0, 0] ![2, 0, -2, 0, 0, 0] (6, 0)) = source26 := by
  decide +kernel

theorem source26_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source26 (momentValues f) = 0 := by
  rw [← source26_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source27 : Sparse := [([0, 1, 0, 0, -2, 0, 1], 18), ([0, 1, 1, 0, -2, 0, 0], 18), ([0, 2, -1, 0, -2, 0, 1], 18), ([0, 2, -1, 1, -2, 0, 0], 18), ([0, 2, 0, -1, -2, 0, 1], 18), ([0, 2, 0, -1, -2, 1, 0], 18), ([0, 2, 0, -1, -1, 0, 0], 18), ([0, 2, 0, 0, -2, -1, 1], -18), ([0, 2, 0, 0, -2, 1, -1], 18), ([0, 2, 0, 0, -1, -1, 0], 18), ([0, 2, 0, 1, -2, -1, 0], 18), ([0, 2, 1, -1, -2, 0, 0], -18), ([0, 2, 1, 0, -2, -1, 0], 18), ([0, 2, 1, 0, -2, 0, -1], 18), ([0, 3, 0, 0, -3, 0, 0], 36), ([1, 1, 0, 0, -2, 0, 1], 18), ([1, 1, 0, 0, -2, 1, 0], -18), ([1, 1, 0, 1, -2, 0, 0], -18), ([1, 1, 1, 0, -2, 0, 0], 18), ([1, 2, -1, 0, -2, 1, 0], 18), ([1, 2, -1, 0, -1, 0, 0], -18), ([1, 2, 0, -1, -1, 0, 0], 18), ([1, 2, 0, 0, -2, -1, 1], -18), ([1, 2, 0, 0, -1, -1, 0], 18), ([1, 2, 0, 0, -1, 0, -1], -18), ([1, 2, 0, 1, -2, 0, -1], 18), ([1, 2, 1, -1, -2, 0, 0], -18)]

theorem source27_checked : normalize (row ![2, 0, 0, -2, 0, 0] ![2, 0, 0, -2, 0, 0] (6, 0)) = source27 := by
  decide +kernel

theorem source27_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source27 (momentValues f) = 0 := by
  rw [← source27_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source28 : Sparse := [([0, 1, 0, 1, 0, -2, 0], 18), ([0, 1, 1, 0, 0, -2, 0], 18), ([0, 2, -1, 0, 0, -2, 1], 18), ([0, 2, -1, 1, 0, -2, 0], 18), ([0, 2, 0, -1, 1, -2, 0], 18), ([0, 2, 0, 0, -1, -2, 1], 18), ([0, 2, 0, 0, -1, -1, 0], 18), ([0, 2, 0, 0, 0, -1, -1], 18), ([0, 2, 0, 0, 1, -2, -1], 18), ([0, 2, 0, 1, -1, -2, 0], -18), ([0, 2, 0, 1, 0, -2, -1], 18), ([0, 2, 1, -1, 0, -2, 0], 18), ([0, 2, 1, 0, -1, -2, 0], 18), ([0, 2, 1, 0, 0, -2, -1], -18), ([0, 3, 0, 0, 0, -3, 0], 36), ([1, 1, 0, 0, 0, -2, 1], -18), ([1, 1, 0, 0, 1, -2, 0], -18), ([1, 1, 0, 1, 0, -2, 0], 18), ([1, 1, 1, 0, 0, -2, 0], 18), ([1, 2, -1, 0, 0, -1, 0], -18), ([1, 2, -1, 0, 1, -2, 0], 18), ([1, 2, 0, -1, 0, -2, 1], 18), ([1, 2, 0, -1, 0, -1, 0], -18), ([1, 2, 0, 0, -1, -1, 0], 18), ([1, 2, 0, 0, 0, -1, -1], 18), ([1, 2, 0, 1, -1, -2, 0], -18), ([1, 2, 1, 0, 0, -2, -1], -18)]

theorem source28_checked : normalize (row ![2, 0, 0, 0, -2, 0] ![2, 0, 0, 0, -2, 0] (6, 0)) = source28 := by
  decide +kernel

theorem source28_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source28 (momentValues f) = 0 := by
  rw [← source28_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source29 : Sparse := [([0, 1, 0, 0, 1, 0, -2], 18), ([0, 1, 0, 1, 0, 0, -2], 18), ([0, 2, -1, 0, 0, 0, -1], 18), ([0, 2, -1, 0, 0, 1, -2], 18), ([0, 2, -1, 0, 1, 0, -2], 18), ([0, 2, -1, 1, 0, 0, -2], -18), ([0, 2, 0, -1, 1, 0, -2], 18), ([0, 2, 0, 0, -1, 1, -2], 18), ([0, 2, 0, 0, 0, -1, -1], 18), ([0, 2, 0, 0, 1, -1, -2], -18), ([0, 2, 0, 1, -1, 0, -2], 18), ([0, 2, 0, 1, 0, -1, -2], 18), ([0, 2, 1, -1, 0, 0, -2], 18), ([0, 2, 1, 0, 0, -1, -2], 18), ([0, 3, 0, 0, 0, 0, -3], 36), ([1, 1, 0, 0, 0, 1, -2], -18), ([1, 1, 0, 0, 1, 0, -2], 18), ([1, 1, 0, 1, 0, 0, -2], 18), ([1, 1, 1, 0, 0, 0, -2], -18), ([1, 2, -1, 0, 0, 0, -1], 18), ([1, 2, -1, 1, 0, 0, -2], -18), ([1, 2, 0, -1, 0, 0, -1], -18), ([1, 2, 0, -1, 0, 1, -2], 18), ([1, 2, 0, 0, -1, 0, -1], -18), ([1, 2, 0, 0, 0, -1, -1], 18), ([1, 2, 0, 0, 1, -1, -2], -18), ([1, 2, 1, 0, -1, 0, -2], 18)]

theorem source29_checked : normalize (row ![2, 0, 0, 0, 0, -2] ![2, 0, 0, 0, 0, -2] (6, 0)) = source29 := by
  decide +kernel

theorem source29_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source29 (momentValues f) = 0 := by
  rw [← source29_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source30 : Sparse := [([0, -2, -1, 0, 0, 1, 2], -36), ([0, -1, -2, 0, 0, 1, 2], 36), ([0, -1, -2, 0, 0, 2, 1], -36), ([0, -1, -1, 0, 0, 0, 2], -36), ([0, -1, -1, 0, 1, 0, 1], -36), ([0, -1, -1, 1, -1, 1, 1], -36), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 1, 0, 1, 0], -36), ([0, -1, 0, 0, -1, 1, 1], -36), ([0, 0, -2, 0, 0, 1, 1], -36), ([0, 0, -1, -1, 0, 1, 1], -36), ([0, 0, -1, 0, -1, 1, 1], 36), ([1, -2, -1, 0, 0, 2, 1], -36), ([1, -2, 0, 0, 0, 1, 1], 36), ([1, -1, -2, 0, 0, 1, 2], 36), ([1, -1, -1, -1, 1, 1, 1], 36), ([1, -1, -1, 0, 0, 0, 2], -36), ([1, -1, -1, 0, 0, 2, 0], 36), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, -1, -1, 1, -1, 1, 1], -36), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, 0, -1, 0, 1, 1], -36), ([1, 0, -2, 0, 0, 1, 1], -36), ([1, 0, -1, 0, -1, 1, 1], 36)]

theorem source30_checked : normalize (row ![-1, -1, 0, 0, 1, 1] ![-1, -1, 0, 0, 1, 1] (-12, 0)) = source30 := by
  decide +kernel

theorem source30_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source30 (momentValues f) = 0 := by
  rw [← source30_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source31 : Sparse := [([0, -2, -1, 0, 1, 0, 2], 36), ([0, -2, -1, 0, 2, 0, 1], -36), ([0, -2, 0, 0, 1, 0, 1], -36), ([0, -1, -2, 0, 1, 0, 2], -36), ([0, -1, -1, 0, 0, 0, 2], -36), ([0, -1, -1, 0, 0, 1, 1], -36), ([0, -1, -1, 1, 0, 0, 1], 36), ([0, -1, -1, 1, 1, -1, 1], -36), ([0, -1, -1, 1, 1, 0, 0], -36), ([0, -1, 0, -1, 1, 0, 1], -36), ([0, -1, 0, 0, 1, -1, 1], 36), ([0, 0, -1, 0, 1, -1, 1], -36), ([1, -2, -1, 0, 1, 0, 2], 36), ([1, -2, 0, 0, 1, 0, 1], -36), ([1, -1, -2, 0, 2, 0, 1], -36), ([1, -1, -1, -1, 1, 1, 1], 36), ([1, -1, -1, 0, 0, 0, 2], -36), ([1, -1, -1, 0, 1, 1, 0], -36), ([1, -1, -1, 0, 2, 0, 0], 36), ([1, -1, -1, 1, 0, 0, 1], 36), ([1, -1, -1, 1, 1, -1, 1], -36), ([1, -1, 0, 0, 1, -1, 1], 36), ([1, 0, -2, 0, 1, 0, 1], 36), ([1, 0, -1, -1, 1, 0, 1], -36)]

theorem source31_checked : normalize (row ![-1, -1, 0, 1, 0, 1] ![-1, -1, 0, 1, 0, 1] (-12, 0)) = source31 := by
  decide +kernel

theorem source31_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source31 (momentValues f) = 0 := by
  rw [← source31_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
