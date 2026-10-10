import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source176 : Sparse := [([0, 0, 0, -1, 0, 0, 1], -9), ([0, 0, 0, -1, 1, -1, 1], 9), ([0, 0, 0, 0, 0, -1, 1], 9), ([0, 0, 1, -1, 0, -1, 1], -9), ([0, 1, -1, -1, 0, -1, 2], 9), ([0, 1, -1, 0, 0, -1, 1], -9), ([0, 1, 0, -2, 0, -1, 2], -9), ([0, 1, 0, -2, 0, 0, 1], 9), ([0, 1, 0, -1, -1, -1, 2], -9), ([0, 1, 0, -1, 0, -2, 2], 9), ([0, 1, 0, -1, 1, -2, 1], -9), ([0, 1, 1, -1, -1, -1, 1], 9), ([1, 0, 0, -1, 0, 0, 1], -9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 1, -1, -1, 0, 0, 1], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, 0, -2, 0, -1, 2], -9), ([1, 1, 0, -2, 0, 0, 1], 9), ([1, 1, 0, -2, 1, -1, 1], -9), ([1, 1, 0, -1, -1, -1, 2], -9), ([1, 1, 0, -1, -1, 0, 1], -9), ([1, 1, 0, 0, -1, -1, 1], -9), ([1, 1, 0, 0, 0, -2, 1], -9), ([1, 1, 1, -2, 0, -1, 1], -9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, 0, -2, 1], -9), ([1, 2, 0, -1, 0, -1, 0], -18)]

theorem source176_checked : normalize (row ![1, 0, -1, 0, -1, 1] ![-1, 0, 0, 0, 0, 1] (0, -3)) = source176 := by
  decide +kernel

theorem source176_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source176 (momentValues f) = 0 := by
  rw [← source176_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source177 : Sparse := [([0, -2, 0, 1, 0, 1, 0], 18), ([0, -1, -1, 1, 0, 2, -1], 9), ([0, -1, -1, 2, 0, 1, -1], 9), ([0, -1, 0, 0, 0, 2, -1], 9), ([0, -1, 0, 0, 1, 1, -1], 9), ([0, -1, 0, 1, -1, 2, -1], -9), ([0, -1, 0, 1, 0, 2, -2], 9), ([0, -1, 0, 1, 1, 0, -1], 9), ([0, -1, 0, 2, -1, 1, -1], 9), ([0, -1, 1, 0, 0, 1, -1], -9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 1, 1, 0, 0, -1], 9), ([0, -1, 1, 1, 0, 1, -2], 9), ([0, 0, 0, 0, 0, 1, -1], 9), ([0, 0, 0, 1, -1, 1, -1], 9), ([1, -2, 0, 1, 0, 1, 0], 18), ([1, -1, -1, 1, 0, 2, -1], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 2, 0, 1, -1], 9), ([1, -1, 0, 0, 0, 2, -1], 9), ([1, -1, 0, 0, 1, 1, -1], 9), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, -1, 0, 1, 1, 1, -2], 9), ([1, -1, 0, 2, -1, 1, -1], 9), ([1, -1, 0, 2, 0, 0, -1], -9), ([1, -1, 0, 2, 0, 1, -2], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 1, 1, 0, 0, -1], 9), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 0, 0, 1, 0, 0, -1], 9)]

theorem source177_checked : normalize (row ![-1, 0, 1, 0, 1, -1] ![1, 0, 0, 0, 0, -1] (3, 3)) = source177 := by
  decide +kernel

theorem source177_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source177 (momentValues f) = 0 := by
  rw [← source177_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source178 : Sparse := [([0, 0, 0, 0, -1, 0, 1], 9), ([0, 0, 1, 0, -1, -1, 1], 9), ([0, 1, -1, 0, -1, 0, 1], 9), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, 0, -1, -1, -1, 2], 9), ([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 1, 0, 0, -2, -1, 2], 9), ([0, 1, 0, 0, -2, 0, 1], 9), ([0, 1, 0, 1, -2, -1, 1], 9), ([0, 1, 0, 1, -1, -2, 1], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, 0, -2, -1, 1], -9), ([0, 1, 1, 0, -1, -2, 1], 9), ([0, 2, 0, 0, -1, -1, 0], 18), ([1, 0, 0, 0, 0, -1, 1], 9), ([1, 0, 0, 1, -1, -1, 1], 9), ([1, 1, -1, 0, -1, -1, 2], 9), ([1, 1, -1, 0, -1, 0, 1], 9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, 0, -1, 0, -1, 1], 9), ([1, 1, 0, 0, -2, 0, 1], 9), ([1, 1, 0, 0, -1, -2, 2], 9), ([1, 1, 0, 0, 0, -2, 1], -9), ([1, 1, 0, 1, -2, -1, 1], 9), ([1, 1, 0, 1, -1, -2, 1], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, 0, -1, -2, 1], 9), ([1, 2, 0, 0, -1, -1, 0], 18)]

theorem source178_checked : normalize (row ![1, 0, 0, -1, -1, 1] ![-1, 0, 0, 0, 0, 1] (3, 3)) = source178 := by
  decide +kernel

theorem source178_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source178 (momentValues f) = 0 := by
  rw [← source178_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source179 : Sparse := [([0, -1, -1, 0, 2, 1, -1], -9), ([0, -1, 0, 0, 0, 2, -1], 9), ([0, -1, 0, 0, 1, 2, -2], -9), ([0, -1, 0, 0, 2, 1, -2], 9), ([0, -1, 0, 1, 1, 0, -1], -9), ([0, -1, 0, 1, 1, 1, -2], 9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, 1, 1, -2], -9), ([0, 0, -1, 0, 1, 1, -1], 9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 0, 0, 0, 0, 1, -1], -9), ([0, 0, 0, 0, 1, 0, -1], 9), ([1, -2, 0, 0, 1, 1, 0], -18), ([1, -1, -1, 0, 1, 2, -1], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, 0, -1, 1, 2, -1], -9), ([1, -1, 0, -1, 2, 1, -1], -9), ([1, -1, 0, 0, 0, 2, -1], 9), ([1, -1, 0, 0, 1, 2, -2], -9), ([1, -1, 0, 0, 2, 0, -1], -9), ([1, -1, 0, 1, 0, 1, -1], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 1, 0, 1, 0, -1], -9), ([1, -1, 1, 0, 1, 1, -2], -9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 0, 0, 0, 0, 1, -1], -9)]

theorem source179_checked : normalize (row ![-1, 0, 0, 1, 1, -1] ![1, 0, 0, 0, 0, -1] (0, -3)) = source179 := by
  decide +kernel

theorem source179_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source179 (momentValues f) = 0 := by
  rw [← source179_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source180 : Sparse := [([0, 1, 0, -1, -1, 0, 1], -9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 1, 0, -1, 0, 0, 0], 9), ([0, 1, 0, 0, -1, 0, 0], -9), ([0, 1, 1, -2, -1, 1, 0], -9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, 0, 0, -1], -9), ([0, 1, 1, 0, -2, 0, 0], 9), ([0, 2, 1, -2, -1, 0, 0], 9), ([0, 2, 1, -1, -2, 0, 0], -9), ([0, 2, 1, -1, -1, -1, 0], -9), ([0, 2, 1, -1, -1, 0, -1], 9), ([1, 0, 2, -1, -1, 0, 0], -18), ([1, 1, 0, -1, -1, 0, 1], -9), ([1, 1, 0, 0, -1, 0, 0], -9), ([1, 1, 1, -2, -1, 0, 1], -9), ([1, 1, 1, -2, 0, 0, 0], -9), ([1, 1, 1, -1, -2, 0, 1], -9), ([1, 1, 1, -1, -2, 1, 0], -9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 0, -1, 0], -9), ([1, 1, 1, 0, -2, 0, 0], 9), ([1, 1, 1, 0, -1, -1, 0], -9), ([1, 1, 1, 0, -1, 0, -1], -9), ([1, 2, 1, -1, -2, 0, 0], -9), ([1, 2, 1, -1, -1, -1, 0], -9)]

theorem source180_checked : normalize (row ![1, 1, -1, -1, 0, 0] ![1, -1, 0, 0, 0, 0] (0, -3)) = source180 := by
  decide +kernel

theorem source180_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source180 (momentValues f) = 0 := by
  rw [← source180_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source181 : Sparse := [([0, -2, -1, 1, 1, 0, 1], 9), ([0, -2, -1, 2, 1, 0, 0], 9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, -1, 0, 1, 1, 0], 9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 1, 2, -1, 0], 9), ([0, -1, -1, 1, 2, 0, -1], 9), ([0, -1, -1, 2, 0, 0, 0], 9), ([0, -1, -1, 2, 1, -1, 0], -9), ([0, -1, -1, 2, 1, 0, -1], 9), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, 0, -2, 1, 1, 0, 0], 18), ([1, -2, -1, 1, 1, 1, 0], 9), ([1, -2, -1, 1, 2, 0, 0], 9), ([1, -1, -1, 0, 1, 0, 1], 9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, -1, 0, 2, 0, 0], -9), ([1, -1, -1, 1, 0, 1, 0], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 1, 2, -1, 0], 9), ([1, -1, -1, 1, 2, 0, -1], 9), ([1, -1, -1, 2, 0, 0, 0], 9), ([1, -1, -1, 2, 1, 0, -1], 9), ([1, -1, 0, 0, 1, 0, 0], 9), ([1, -1, 0, 1, 1, 0, -1], 9), ([1, 0, -2, 1, 1, 0, 0], 18)]

theorem source181_checked : normalize (row ![-1, -1, 1, 1, 0, 0] ![-1, 1, 0, 0, 0, 0] (3, 3)) = source181 := by
  decide +kernel

theorem source181_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source181 (momentValues f) = 0 := by
  rw [← source181_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source182 : Sparse := [([0, 0, 2, -1, 0, -1, 0], 18), ([0, 1, 0, -1, 0, -1, 1], 9), ([0, 1, 0, 0, 0, -1, 0], 9), ([0, 1, 1, -2, 0, -1, 1], 9), ([0, 1, 1, -2, 1, -1, 0], 9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, -1, 0, 0], 9), ([0, 1, 1, -1, 0, -2, 1], -9), ([0, 1, 1, -1, 0, 0, -1], 9), ([0, 1, 1, -1, 1, -2, 0], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([0, 1, 1, 0, 0, -2, 0], 9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 2, 1, -1, -1, -1, 0], 9), ([0, 2, 1, -1, 0, -2, 0], 9), ([1, 0, 2, -1, 0, -1, 0], 18), ([1, 1, 0, -1, 0, 0, 0], 9), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 1, 1, -2, 0, -1, 1], 9), ([1, 1, 1, -2, 0, 0, 0], -9), ([1, 1, 1, -2, 1, -1, 0], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, 0, 0], 9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, -1, 1, -2, 0], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, 0, -2, 0], 9), ([1, 1, 1, 0, 0, -1, -1], 9), ([1, 2, 1, -2, 0, -1, 0], 9), ([1, 2, 1, -1, 0, -1, -1], 9)]

theorem source182_checked : normalize (row ![1, 1, -1, 0, -1, 0] ![1, -1, 0, 0, 0, 0] (3, 3)) = source182 := by
  decide +kernel

theorem source182_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source182 (momentValues f) = 0 := by
  rw [← source182_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source183 : Sparse := [([0, -2, -1, 1, 0, 1, 1], -9), ([0, -2, -1, 1, 0, 2, 0], 9), ([0, -2, -1, 1, 1, 1, 0], 9), ([0, -2, -1, 2, 0, 1, 0], -9), ([0, -1, -1, 0, 1, 1, 0], -9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 0, 2, -1], -9), ([0, -1, -1, 2, 0, 0, 0], 9), ([0, -1, 0, 0, 0, 1, 0], 9), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 1, 0, 1, -1], 9), ([1, -2, -1, 1, 0, 1, 1], -9), ([1, -2, -1, 2, 0, 1, 0], -9), ([1, -1, -1, 0, 0, 1, 1], -9), ([1, -1, -1, 0, 0, 2, 0], -9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, -1, 2, 0], -9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 1, 1, 0, 0], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, -1, -1, 2, -1, 1, 0], -9), ([1, -1, -1, 2, 0, 0, 0], 9), ([1, -1, -1, 2, 0, 1, -1], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, 0, -2, 1, 0, 1, 0], -18)]

theorem source183_checked : normalize (row ![-1, -1, 1, 0, 1, 0] ![-1, 1, 0, 0, 0, 0] (0, -3)) = source183 := by
  decide +kernel

theorem source183_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source183 (momentValues f) = 0 := by
  rw [← source183_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
