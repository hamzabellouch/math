import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source264 : Sparse := [([0, -2, -1, 1, 1, 0, 1], 9), ([0, -2, -1, 1, 1, 1, 0], 9), ([0, -1, -2, 1, 1, 0, 1], -9), ([0, -1, -2, 1, 1, 1, 0], 9), ([0, -1, -2, 1, 2, 0, 0], 9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 1, 2, -1, 0], 9), ([0, -1, -1, 2, 0, 0, 0], 18), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, 0, -2, 1, 1, 0, 0], 9), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, -1, 1, 1, 0, -1], 9), ([1, -2, -1, 1, 1, 0, 1], 9), ([1, -2, -1, 1, 1, 1, 0], 9), ([1, -2, -1, 1, 2, 0, 0], 9), ([1, -2, 0, 1, 1, 0, 0], -9), ([1, -1, -2, 1, 1, 1, 0], 9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 1, 2, 0, -1], 9), ([1, -1, -1, 2, 0, 0, 0], 18), ([1, -1, 0, 0, 1, 0, 0], 9), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, 0, -2, 1, 1, 0, 0], 9), ([1, 0, -1, 1, 1, 0, -1], 9)]

theorem source264_checked : normalize (row ![-1, -1, 1, 1, 0, 0] ![0, 0, -1, 1, 0, 0] (3, 3)) = source264 := by
  decide +kernel

theorem source264_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source264 (momentValues f) = 0 := by
  rw [← source264_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source265 : Sparse := [([0, 0, 1, -1, -1, 1, 0], -9), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 1, 0, 0, -1, 0, 0], -9), ([0, 1, 1, -1, -2, 0, 1], -9), ([0, 1, 1, -1, -2, 1, 0], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 1, 2, -1, -2, 0, 0], 9), ([0, 1, 2, -1, -1, 0, -1], -9), ([0, 2, 0, -1, -1, 0, 0], 9), ([0, 2, 1, -1, -2, 0, 0], -9), ([1, 0, 1, -1, -1, 0, 1], -9), ([1, 0, 2, -1, -1, 0, 0], -9), ([1, 1, 0, -1, -1, 0, 1], -9), ([1, 1, 0, -1, -1, 1, 0], -9), ([1, 1, 0, 0, -1, 0, 0], -9), ([1, 1, 1, -2, 0, 0, 0], -18), ([1, 1, 1, -1, -2, 0, 1], -9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 1, 2, -1, -1, -1, 0], -9), ([1, 2, 0, -1, -1, 0, 0], 9), ([1, 2, 1, -1, -2, 0, 0], -9), ([1, 2, 1, -1, -1, -1, 0], -9), ([1, 2, 1, -1, -1, 0, -1], -9)]

theorem source265_checked : normalize (row ![1, 1, -1, -1, 0, 0] ![0, 0, 1, -1, 0, 0] (0, -3)) = source265 := by
  decide +kernel

theorem source265_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source265 (momentValues f) = 0 := by
  rw [← source265_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source266 : Sparse := [([0, -2, 0, 1, 2, -1, 0], 9), ([0, -2, 1, 1, 1, -1, 0], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 1, 2, -1, 0], -9), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 0, 0, 1, 0, 0], 9), ([0, -1, 0, 1, 1, 0, -1], -9), ([0, -1, 0, 1, 2, -2, 0], -9), ([0, -1, 0, 1, 2, -1, -1], 9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 0, 0, 1, 1, -2, 0], 9), ([1, -2, 0, 1, 1, -1, 1], -9), ([1, -2, 0, 1, 1, 0, 0], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 1, 2, -1, 0], -9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, -1, 0, 1, 1, -2, 1], -9), ([1, -1, 0, 1, 2, -2, 0], -9), ([1, -1, 0, 2, 0, -1, 0], -18), ([1, -1, 1, 1, 1, -2, 0], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 0, 0, 1, 1, -2, 0], 9), ([1, 0, 0, 1, 1, -1, -1], -9)]

theorem source266_checked : normalize (row ![-1, 0, 1, 1, -1, 0] ![0, 0, -1, 1, 0, 0] (0, -3)) = source266 := by
  decide +kernel

theorem source266_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source266 (momentValues f) = 0 := by
  rw [← source266_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source267 : Sparse := [([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 1, -1, -1, 1, 0], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, -1, 2, 0], 9), ([0, 1, -1, 0, -1, 1, 0], 9), ([0, 1, 0, -2, 0, 1, 0], 18), ([0, 1, 0, -1, -2, 1, 1], 9), ([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 0, -1, -1, 2, -1], 9), ([0, 1, 0, 0, -1, 0, 0], 9), ([0, 1, 1, -1, -1, 0, 0], 9), ([0, 2, -1, -1, -1, 1, 0], -9), ([0, 2, 0, -1, -2, 1, 0], 9), ([0, 2, 0, -1, -1, 0, 0], 9), ([0, 2, 0, -1, -1, 1, -1], 9), ([1, 0, 0, -1, -1, 1, 1], 9), ([1, 0, 0, -1, -1, 2, 0], -9), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 2, 0], 9), ([1, 1, 0, -2, 0, 1, 0], 18), ([1, 1, 0, -1, -2, 2, 0], 9), ([1, 1, 0, -1, -1, 2, -1], 9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 1, 1, -1, -2, 1, 0], 9), ([1, 1, 1, -1, -1, 0, 0], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 2, 0, -1, -1, 0, 0], 9), ([1, 2, 0, -1, -1, 1, -1], 9)]

theorem source267_checked : normalize (row ![1, 0, -1, -1, 1, 0] ![0, 0, 1, -1, 0, 0] (3, 3)) = source267 := by
  decide +kernel

theorem source267_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source267 (momentValues f) = 0 := by
  rw [← source267_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source268 : Sparse := [([0, -2, 0, 1, 2, 0, -1], 9), ([0, -2, 1, 1, 1, 0, -1], -9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, -1, -1, 1, 2, 0, -1], -9), ([0, -1, 0, 0, 1, 0, 0], -9), ([0, -1, 0, 0, 1, 1, -1], 9), ([0, -1, 0, 1, 1, 1, -2], -9), ([0, -1, 0, 1, 2, -1, -1], -9), ([0, -1, 0, 1, 2, 0, -2], 9), ([0, -1, 1, 0, 1, 0, -1], 9), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 0, 0, 1, 1, -1, -1], 9), ([1, -2, 0, 1, 1, 0, 0], -9), ([1, -2, 0, 1, 1, 1, -1], -9), ([1, -1, -1, 1, 1, 0, 0], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 1, 2, 0, -1], -9), ([1, -1, 0, 0, 1, 0, 0], -9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, -1, 0, 1, 2, -1, -1], -9), ([1, -1, 0, 2, 0, 0, -1], -18), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 1, 1, 1, 0, -2], -9), ([1, 0, -1, 1, 1, 0, -1], -9), ([1, 0, 0, 0, 1, 0, -1], -9), ([1, 0, 0, 1, 1, -1, -1], 9), ([1, 0, 0, 1, 1, 0, -2], -9)]

theorem source268_checked : normalize (row ![-1, 0, 1, 1, 0, -1] ![0, 0, -1, 1, 0, 0] (0, -3)) = source268 := by
  decide +kernel

theorem source268_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source268 (momentValues f) = 0 := by
  rw [← source268_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source269 : Sparse := [([0, 0, 0, -1, -1, 0, 2], 9), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 1, -1, -1, -1, 0, 2], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, 0, -1, 0, 1], 9), ([0, 1, 0, -2, 0, 0, 1], 18), ([0, 1, 0, -1, -2, 0, 2], 9), ([0, 1, 0, -1, -1, -1, 2], -9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 1, 0, 0, -1, -1, 1], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 2, -1, -1, -1, 0, 1], -9), ([0, 2, 0, -1, -2, 0, 1], 9), ([0, 2, 0, -1, -1, -1, 1], 9), ([0, 2, 0, -1, -1, 0, 0], 9), ([1, 0, 0, -1, -1, 0, 2], 9), ([1, 0, 0, -1, -1, 1, 1], -9), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 1, -1, -1, 0, 1], 9), ([1, 1, -1, -1, -1, 0, 2], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, 0, -2, 0, 0, 1], 18), ([1, 1, 0, -1, -2, 1, 1], 9), ([1, 1, 0, -1, -1, 1, 0], 9), ([1, 1, 0, 0, -1, 0, 0], 9), ([1, 1, 1, -1, -2, 0, 1], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, 0, 0], -9), ([1, 2, 0, -1, -1, -1, 1], 9), ([1, 2, 0, -1, -1, 0, 0], 9)]

theorem source269_checked : normalize (row ![1, 0, -1, -1, 0, 1] ![0, 0, 1, -1, 0, 0] (3, 3)) = source269 := by
  decide +kernel

theorem source269_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source269 (momentValues f) = 0 := by
  rw [← source269_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source270 : Sparse := [([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, 0, -2, 1, 1, -1, 1], -9), ([0, 0, -2, 1, 1, 0, 0], 9), ([0, 0, -2, 1, 2, -1, 0], 9), ([0, 0, -1, 0, 1, -1, 1], 9), ([0, 0, -1, 1, 1, -2, 1], 9), ([0, 0, -1, 1, 2, -2, 0], 9), ([0, 0, -1, 2, 0, -1, 0], 18), ([0, 0, 0, 1, 1, -2, 0], 9), ([0, 0, 0, 1, 1, -1, -1], 9), ([0, 1, -2, 1, 1, -1, 0], 9), ([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, -1, 1, 1, -2, 0], -9), ([0, 1, -1, 1, 1, -1, -1], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 1, 0, 0], 9), ([1, -1, -1, 1, 2, -1, 0], 9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, 0, -2, 1, 1, 0, 0], 9), ([1, 0, -1, 0, 1, 0, 0], 9), ([1, 0, -1, 1, 1, -2, 1], 9), ([1, 0, -1, 1, 1, 0, -1], -9), ([1, 0, -1, 1, 2, -1, -1], 9), ([1, 0, -1, 2, 0, -1, 0], 18), ([1, 0, 0, 0, 1, -1, 0], 9), ([1, 0, 0, 1, 1, -2, 0], 9), ([1, 0, 0, 1, 1, -1, -1], 9), ([1, 1, -2, 1, 1, -1, 0], 9), ([1, 1, -1, 1, 1, -1, -1], 9)]

theorem source270_checked : normalize (row ![0, -1, 1, 1, -1, 0] ![0, 0, -1, 1, 0, 0] (3, 3)) = source270 := by
  decide +kernel

theorem source270_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source270 (momentValues f) = 0 := by
  rw [← source270_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source271 : Sparse := [([0, -1, 1, -1, -1, 2, 0], -9), ([0, -1, 1, 0, -1, 1, 0], 9), ([0, 0, 0, 0, -1, 1, 0], -9), ([0, 0, 1, -1, -2, 1, 1], -9), ([0, 0, 1, -1, -2, 2, 0], 9), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, 0, -1, 0, 0], -9), ([0, 0, 1, 0, -1, 1, -1], 9), ([0, 0, 2, -1, -2, 1, 0], 9), ([0, 0, 2, -1, -1, 1, -1], -9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 1, 1, -1, -2, 1, 0], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 2, -1, -1, 1, 0], -9), ([1, 0, 0, -1, -1, 1, 1], -9), ([1, 0, 0, -1, -1, 2, 0], -9), ([1, 0, 0, 0, -1, 1, 0], -9), ([1, 0, 1, -2, 0, 1, 0], -18), ([1, 0, 1, -1, -2, 1, 1], -9), ([1, 0, 1, -1, -1, 0, 1], 9), ([1, 0, 1, -1, -1, 2, -1], -9), ([1, 0, 1, 0, -1, 0, 0], -9), ([1, 0, 2, -1, -1, 0, 0], -9), ([1, 1, 0, -1, -1, 1, 0], 9), ([1, 1, 1, -1, -2, 1, 0], -9), ([1, 1, 1, -1, -1, 0, 0], -9), ([1, 1, 1, -1, -1, 1, -1], -9)]

theorem source271_checked : normalize (row ![0, 1, -1, -1, 1, 0] ![0, 0, 1, -1, 0, 0] (0, -3)) = source271 := by
  decide +kernel

theorem source271_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source271 (momentValues f) = 0 := by
  rw [← source271_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
