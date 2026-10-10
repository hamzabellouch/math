import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source272 : Sparse := [([0, -1, -1, 1, 2, 0, -1], 9), ([0, -1, 0, 1, 1, 0, -1], -9), ([0, 0, -2, 1, 1, 0, 0], 9), ([0, 0, -2, 1, 2, 0, -1], -9), ([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 1, 1, -1], 9), ([0, 0, -1, 1, 1, 1, -2], -9), ([0, 0, -1, 1, 2, -1, -1], -9), ([0, 0, -1, 1, 2, 0, -2], 9), ([0, 0, 0, 0, 1, 0, -1], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 1, -1, 1, 1, -1, -1], 9), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, 0, -2, 1, 1, 0, 0], 9), ([1, 0, -2, 1, 1, 1, -1], -9), ([1, 0, -2, 1, 2, 0, -1], -9), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 0, -1, 1, 2, -1, -1], -9), ([1, 0, -1, 2, 0, 0, -1], -18), ([1, 0, 0, 1, 1, -1, -1], -9), ([1, 0, 0, 1, 1, 0, -2], -9), ([1, 1, -2, 1, 1, 0, -1], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 1, 1, 0, -2], -9)]

theorem source272_checked : normalize (row ![0, -1, 1, 1, 0, -1] ![0, 0, -1, 1, 0, 0] (0, -3)) = source272 := by
  decide +kernel

theorem source272_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source272 (momentValues f) = 0 := by
  rw [← source272_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source273 : Sparse := [([0, -1, 1, -1, -1, 0, 2], 9), ([0, -1, 2, -1, -1, 0, 1], 9), ([0, 0, 0, -1, -1, 0, 2], 9), ([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 0, 0, -1, 0, 1], 9), ([0, 0, 1, -2, 0, 0, 1], 18), ([0, 0, 1, -1, -2, 0, 2], 9), ([0, 0, 1, -1, -1, -1, 2], -9), ([0, 0, 1, -1, -1, 1, 0], 9), ([0, 0, 1, 0, -1, -1, 1], 9), ([0, 0, 2, -1, -1, -1, 1], 9), ([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 1, -1, -2, 0, 1], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, -1, 0, 0], 9), ([1, -1, 1, -1, -1, 0, 2], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 2, -1, -1, 0, 1], 9), ([1, 0, 0, -1, -1, 0, 2], 9), ([1, 0, 0, -1, -1, 1, 1], 9), ([1, 0, 1, -2, 0, 0, 1], 18), ([1, 0, 1, -1, -2, 1, 1], 9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 2, -1, -2, 0, 1], 9), ([1, 0, 2, -1, -1, -1, 1], 9), ([1, 0, 2, -1, -1, 0, 0], -9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, 0, 0], 9)]

theorem source273_checked : normalize (row ![0, 1, -1, -1, 0, 1] ![0, 0, 1, -1, 0, 0] (3, 3)) = source273 := by
  decide +kernel

theorem source273_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source273 (momentValues f) = 0 := by
  rw [← source273_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source274 : Sparse := [([0, -1, 0, 1, 1, -1, 0], 9), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, -1, 1, 1, 0, -1], 9), ([0, 0, -1, 1, 2, -1, -1], 9), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 0, 0, 1, 1, -2, 0], 9), ([0, 0, 0, 1, 2, -2, -1], 9), ([0, 0, 0, 2, 0, -1, -1], 18), ([0, 0, 1, 1, 1, -2, -1], 9), ([0, 0, 1, 1, 1, -1, -2], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 1, 0, 1, 1, -2, -1], -9), ([0, 1, 0, 1, 1, -1, -2], 9), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, -1, 0, 1, 2, -1, -1], 9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, 0, 0, 1, 0, -1], 9), ([1, 0, 0, 1, 1, -2, 0], 9), ([1, 0, 0, 1, 1, 0, -2], -9), ([1, 0, 0, 1, 2, -1, -2], 9), ([1, 0, 0, 2, 0, -1, -1], 18), ([1, 0, 1, 0, 1, -1, -1], 9), ([1, 0, 1, 1, 1, -2, -1], 9), ([1, 0, 1, 1, 1, -1, -2], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, 1, 1, -1, -2], 9)]

theorem source274_checked : normalize (row ![0, 0, 1, 1, -1, -1] ![0, 0, -1, 1, 0, 0] (3, 3)) = source274 := by
  decide +kernel

theorem source274_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source274 (momentValues f) = 0 := by
  rw [← source274_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source275 : Sparse := [([0, -1, 0, -1, -1, 2, 1], -9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, 0, -1, -2, 1, 2], -9), ([0, 0, 0, -1, -2, 2, 1], 9), ([0, 0, 0, -1, -1, 0, 2], 9), ([0, 0, 0, 0, -1, 0, 1], -9), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 0, 1, -1, -2, 1, 1], 9), ([0, 0, 1, -1, -1, 1, 0], -9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, 0, -1, -2, 1, 1], -9), ([1, -1, 0, -1, -1, 1, 2], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, 0, -1, -1, -1, 1, 2], -9), ([1, 0, -1, -1, -1, 2, 1], -9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, 0, -2, 0, 1, 1], -18), ([1, 0, 0, -1, -2, 1, 2], -9), ([1, 0, 0, -1, -1, 0, 2], 9), ([1, 0, 0, -1, -1, 2, 0], -9), ([1, 0, 0, 0, -1, 0, 1], -9), ([1, 0, 1, -1, -1, 0, 1], -9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, 0, -1, -2, 1, 1], -9), ([1, 1, 0, -1, -1, 0, 1], -9), ([1, 1, 0, -1, -1, 1, 0], -9)]

theorem source275_checked : normalize (row ![0, 0, -1, -1, 1, 1] ![0, 0, 1, -1, 0, 0] (0, -3)) = source275 := by
  decide +kernel

theorem source275_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source275 (momentValues f) = 0 := by
  rw [← source275_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source276 : Sparse := [([0, -2, -1, 1, 0, 1, 1], -9), ([0, -2, -1, 1, 0, 2, 0], 9), ([0, -2, -1, 1, 1, 1, 0], 9), ([0, -2, 0, 1, 0, 1, 0], 9), ([0, -1, -2, 1, 0, 1, 1], 9), ([0, -1, -2, 1, 1, 1, 0], 9), ([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, -1, 2, 0], 9), ([0, -1, -1, 2, 0, 0, 0], 18), ([0, -1, 0, 0, 0, 1, 0], 9), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 0, 1, 0, 1, -1], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, -1, 1, 0, 1, -1], 9), ([1, -2, -1, 1, 1, 1, 0], 9), ([1, -2, 0, 1, 0, 1, 0], 9), ([1, -1, -2, 1, 0, 1, 1], 9), ([1, -1, -2, 1, 0, 2, 0], 9), ([1, -1, -2, 1, 1, 1, 0], 9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, 2, -1], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 2, 0, 0, 0], 18), ([1, -1, 0, 1, 0, 1, -1], 9), ([1, 0, -2, 1, 0, 1, 0], -9), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, -1, 1, 0], 9), ([1, 0, -1, 1, 0, 1, -1], 9)]

theorem source276_checked : normalize (row ![-1, -1, 1, 0, 1, 0] ![0, 0, -1, 0, 1, 0] (3, 3)) = source276 := by
  decide +kernel

theorem source276_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source276 (momentValues f) = 0 := by
  rw [← source276_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source277 : Sparse := [([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 2, -1, 0, -1, 0], 9), ([0, 1, 0, -1, 1, -1, 0], -9), ([0, 1, 0, 0, 0, -1, 0], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, 0, -2, 1], -9), ([0, 1, 1, -1, 1, -2, 0], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 2, -1, 0, -2, 0], -9), ([0, 2, 1, -1, 0, -2, 0], 9), ([0, 2, 1, -1, 0, -1, -1], -9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 0, 1, -1, 1, -1, 0], -9), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 2, -1, 0, -1, 0], 9), ([1, 1, 0, -1, 0, -1, 1], -9), ([1, 1, 1, -2, 0, 0, 0], -18), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, 0, -2, 1], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 1, 2, -1, -1, -1, 0], -9), ([1, 1, 2, -1, 0, -2, 0], -9), ([1, 1, 2, -1, 0, -1, -1], -9), ([1, 2, 0, -1, 0, -1, 0], -9), ([1, 2, 1, -1, -1, -1, 0], -9)]

theorem source277_checked : normalize (row ![1, 1, -1, 0, -1, 0] ![0, 0, 1, 0, -1, 0] (0, -3)) = source277 := by
  decide +kernel

theorem source277_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source277 (momentValues f) = 0 := by
  rw [← source277_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source278 : Sparse := [([0, -2, 0, 1, -1, 1, 1], -9), ([0, -2, 0, 1, -1, 2, 0], 9), ([0, -2, 0, 1, 0, 1, 0], 9), ([0, -2, 1, 1, -1, 1, 0], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, -1, 0, 1, -2, 1, 1], 9), ([0, -1, 0, 1, -2, 2, 0], 9), ([0, -1, 0, 2, -1, 0, 0], 18), ([0, -1, 1, 0, -1, 1, 0], 9), ([0, -1, 1, 1, -2, 1, 0], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, 0, 0, 1, -2, 1, 0], 9), ([0, 0, 0, 1, -1, 1, -1], 9), ([1, -2, 0, 1, 0, 1, 0], 9), ([1, -2, 1, 1, -1, 1, 0], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, -1, 2, 0], 9), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, 0, 0, 0, 1, 0], 9), ([1, -1, 0, 1, -2, 1, 1], 9), ([1, -1, 0, 1, -1, 2, -1], 9), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, -1, 0, 2, -1, 0, 0], 18), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, 0, -1, 1, -1, 1, 0], -9), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 0, 0, 1, -2, 1, 0], 9), ([1, 0, 0, 1, -1, 1, -1], 9)]

theorem source278_checked : normalize (row ![-1, 0, 1, -1, 1, 0] ![0, 0, -1, 0, 1, 0] (3, 3)) = source278 := by
  decide +kernel

theorem source278_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source278 (momentValues f) = 0 := by
  rw [← source278_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source279 : Sparse := [([0, 0, 0, 0, 1, -1, 0], -9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 1, -1, -1, 2, -1, 0], -9), ([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 1, 0, -1, 1, -2, 1], -9), ([0, 1, 0, -1, 2, -2, 0], 9), ([0, 1, 0, 0, 0, -1, 0], -9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 1, 1, -1, 1, -2, 0], -9), ([0, 2, 0, -1, 1, -2, 0], 9), ([0, 2, 0, -1, 1, -1, -1], -9), ([1, 0, 0, -1, 1, -1, 1], -9), ([1, 0, 0, -1, 2, -1, 0], -9), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 0, 1, -1, 1, -1, 0], 9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, 0, -2, 1, 0, 0], -18), ([1, 1, 0, -1, 0, -1, 1], 9), ([1, 1, 0, -1, 1, -2, 1], -9), ([1, 1, 0, -1, 2, -1, -1], -9), ([1, 1, 0, 0, 0, -1, 0], -9), ([1, 1, 1, -1, 0, -1, 0], -9), ([1, 1, 1, -1, 1, -2, 0], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 2, -1, -1, 1, -1, 0], -9), ([1, 2, 0, -1, 0, -1, 0], -9)]

theorem source279_checked : normalize (row ![1, 0, -1, 1, -1, 0] ![0, 0, 1, 0, -1, 0] (0, -3)) = source279 := by
  decide +kernel

theorem source279_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source279 (momentValues f) = 0 := by
  rw [← source279_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
