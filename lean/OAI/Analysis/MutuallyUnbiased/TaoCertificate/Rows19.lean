import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source152 : Sparse := [([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 0, 0, 0, 1, 0, -1], -9), ([0, 0, 1, -1, 1, 0, -1], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, -1, 2, 0, -1], -9), ([0, 1, 0, -2, 2, 0, -1], 9), ([0, 1, 0, -1, 1, -1, 0], -9), ([0, 1, 0, -1, 2, -1, -1], 9), ([0, 1, 0, -1, 2, 0, -2], -9), ([0, 1, 0, 0, 1, 0, -2], 9), ([0, 1, 1, -2, 1, 0, -1], -9), ([1, 0, 0, -1, 1, 1, -1], -9), ([1, 0, 0, 0, 1, 0, -1], -9), ([1, 1, -1, -1, 1, 0, 0], -9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, -1, 2, 0, -1], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, 0, -2, 1, 0, 0], -9), ([1, 1, 0, -2, 1, 1, -1], -9), ([1, 1, 0, -1, 1, 1, -2], -9), ([1, 1, 0, -1, 2, 0, -2], -9), ([1, 1, 0, 0, 1, -1, -1], -9), ([1, 1, 0, 0, 1, 0, -2], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, -1, 1, 0, -2], -9), ([1, 2, 0, -1, 0, 0, -1], -18)]

theorem source152_checked : normalize (row ![1, 0, -1, 1, 0, -1] ![-1, 0, 0, 1, 0, 0] (0, -3)) = source152 := by
  decide +kernel

theorem source152_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source152 (momentValues f) = 0 := by
  rw [← source152_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source153 : Sparse := [([0, -2, 0, 1, 0, 0, 1], 18), ([0, -1, -1, 1, -1, 0, 2], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 2, -1, 0, 1], -9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, -1, 0, 1, -2, 1, 1], 9), ([0, -1, 0, 1, -1, -1, 2], 9), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 0, 2, -2, 0, 1], 9), ([0, -1, 0, 2, -1, -1, 1], 9), ([0, -1, 0, 2, -1, 0, 0], 9), ([0, -1, 1, 0, -1, 0, 1], 9), ([0, -1, 1, 1, -1, 0, 0], 9), ([0, 0, -1, 1, -1, 0, 1], 9), ([0, 0, 0, 1, -1, 0, 0], 9), ([1, -2, 0, 1, 0, 0, 1], 18), ([1, -1, -1, 1, -1, 0, 2], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, 0, 0, -1, 0, 2], -9), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, -1, 0, 1, -2, 0, 2], 9), ([1, -1, 0, 1, -1, -1, 2], 9), ([1, -1, 0, 2, -1, -1, 1], 9), ([1, -1, 0, 2, -1, 0, 0], 9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 1, 1, -2, 0, 1], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, -1, 0, 0], 9), ([1, 0, 0, 0, -1, 0, 1], 9), ([1, 0, 0, 1, -1, -1, 1], 9)]

theorem source153_checked : normalize (row ![-1, 0, 1, -1, 0, 1] ![1, 0, 0, -1, 0, 0] (3, 3)) = source153 := by
  decide +kernel

theorem source153_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source153 (momentValues f) = 0 := by
  rw [← source153_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source154 : Sparse := [([0, 0, 0, 0, 1, 0, -1], 9), ([0, 0, 0, 1, 1, -1, -1], 9), ([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 1, -1, 0, 2, -1, -1], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, -1, 1, -1, 0], 9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 1, 0, 0, 1, 0, -2], 9), ([0, 1, 0, 0, 2, -1, -2], 9), ([0, 1, 0, 1, 1, -2, -1], 9), ([0, 1, 0, 1, 1, -1, -2], -9), ([0, 1, 1, 0, 1, -2, -1], 9), ([0, 1, 1, 0, 1, -1, -2], 9), ([0, 2, 0, 0, 0, -1, -1], 18), ([1, 0, 0, 0, 1, -1, 0], 9), ([1, 0, 1, 0, 1, -1, -1], 9), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 1, 0, -1, 1, 0, -1], 9), ([1, 1, 0, -1, 2, -1, -1], 9), ([1, 1, 0, 0, 1, -2, 0], -9), ([1, 1, 0, 0, 1, 0, -2], 9), ([1, 1, 0, 0, 2, -2, -1], 9), ([1, 1, 0, 1, 1, -2, -1], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, 1, -2, -1], 9), ([1, 1, 1, 0, 1, -1, -2], 9), ([1, 2, 0, 0, 0, -1, -1], 18)]

theorem source154_checked : normalize (row ![1, 0, 0, 1, -1, -1] ![-1, 0, 0, 1, 0, 0] (3, 3)) = source154 := by
  decide +kernel

theorem source154_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source154 (momentValues f) = 0 := by
  rw [← source154_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source155 : Sparse := [([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, 0, -1, -1, 1, 2], -9), ([0, -1, 0, 0, -2, 1, 2], 9), ([0, -1, 0, 0, -2, 2, 1], -9), ([0, -1, 0, 0, -1, 2, 0], 9), ([0, -1, 0, 1, -2, 1, 1], -9), ([0, -1, 1, 0, -2, 1, 1], 9), ([0, -1, 1, 0, -1, 0, 1], -9), ([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 0, 0, -1, 0, 1], 9), ([0, 0, 0, 0, -1, 1, 0], -9), ([1, -2, 0, 0, 0, 1, 1], -18), ([1, -1, -1, 0, -1, 1, 2], -9), ([1, -1, -1, 0, -1, 2, 1], -9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, 0, -1, -1, 2, 1], -9), ([1, -1, 0, 0, -2, 2, 1], -9), ([1, -1, 0, 0, -1, 0, 2], -9), ([1, -1, 0, 0, -1, 2, 0], 9), ([1, -1, 0, 1, -2, 1, 1], -9), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, 0, 0, -1, 1, 0], -9)]

theorem source155_checked : normalize (row ![-1, 0, 0, -1, 1, 1] ![1, 0, 0, -1, 0, 0] (0, -3)) = source155 := by
  decide +kernel

theorem source155_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source155 (momentValues f) = 0 := by
  rw [← source155_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source156 : Sparse := [([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 1, -2, -1, 0, 1, 1], 9), ([0, 1, -2, -1, 0, 2, 0], 9), ([0, 1, -2, -1, 1, 1, 0], -9), ([0, 1, -2, 0, 0, 1, 0], 9), ([0, 1, -1, -2, 0, 1, 1], -9), ([0, 1, -1, -2, 0, 2, 0], 9), ([0, 1, -1, -2, 1, 1, 0], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, 0, -2, 0, 1, 0], 9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 2, -1, -1, 0, 0, 0], 18), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, 0, -1, 0, 1, 0], 9), ([1, 1, -2, -1, 0, 1, 1], 9), ([1, 1, -2, 0, 0, 1, 0], 9), ([1, 1, -1, -2, 1, 1, 0], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 2, 0], 9), ([1, 1, -1, -1, 0, 2, -1], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, -1, 1, 0], -9), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, 0, -2, 0, 1, 0], 9), ([1, 1, 0, -1, -1, 1, 0], 9), ([1, 1, 0, -1, 0, 1, -1], -9), ([1, 2, -1, -1, 0, 0, 0], 18)]

theorem source156_checked : normalize (row ![1, -1, -1, 0, 1, 0] ![-1, 0, 0, 0, 1, 0] (3, 3)) = source156 := by
  decide +kernel

theorem source156_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source156 (momentValues f) = 0 := by
  rw [← source156_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source157 : Sparse := [([0, -1, 0, 1, 0, -1, 1], 9), ([0, -1, 1, 0, 1, -1, 0], 9), ([0, -1, 1, 1, 0, -2, 1], -9), ([0, -1, 1, 1, 1, -2, 0], -9), ([0, -1, 1, 2, 0, -2, 0], 9), ([0, -1, 1, 2, 0, -1, -1], -9), ([0, -1, 2, 1, -1, -1, 0], -9), ([0, -1, 2, 1, 0, -2, 0], 9), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 0, 1, 1, 0, -1, -1], 9), ([1, -2, 1, 1, 0, 0, 0], -18), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, -1, 0, 2, 0, -1, 0], -9), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 0, 1, -1, 0], 9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, -1, 1, 1, 0, -2, 1], -9), ([1, -1, 1, 1, 1, -2, 0], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 1, 2, -1, -1, 0], -9), ([1, -1, 2, 0, 0, -1, 0], -9), ([1, -1, 2, 1, 0, -1, -1], -9), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 0, 1, 0, 0, -1, 0], -9)]

theorem source157_checked : normalize (row ![-1, 1, 1, 0, -1, 0] ![1, 0, 0, 0, -1, 0] (0, -3)) = source157 := by
  decide +kernel

theorem source157_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source157 (momentValues f) = 0 := by
  rw [← source157_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source158 : Sparse := [([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 1, -2, 0, -1, 2, 0], -9), ([0, 1, -2, 0, 0, 1, 0], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, -1, 2, 0], -9), ([0, 1, -1, 0, -2, 2, 0], 9), ([0, 1, -1, 0, -1, 2, -1], 9), ([0, 1, -1, 1, -2, 1, 0], -9), ([0, 1, 0, 0, -1, 1, -1], -9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 1, -2, 0, -1, 1, 1], -9), ([1, 1, -2, 0, -1, 2, 0], -9), ([1, 1, -2, 0, 0, 1, 0], 9), ([1, 1, -2, 1, -1, 1, 0], -9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 2, 0], -9), ([1, 1, -1, -1, 0, 1, 0], -9), ([1, 1, -1, 0, -2, 1, 1], -9), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, 0, -1, -1, 1, 0], -9), ([1, 1, 0, 0, -2, 1, 0], -9), ([1, 2, -1, 0, -1, 0, 0], -18)]

theorem source158_checked : normalize (row ![1, -1, 0, -1, 1, 0] ![-1, 0, 0, 0, 1, 0] (0, -3)) = source158 := by
  decide +kernel

theorem source158_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source158 (momentValues f) = 0 := by
  rw [← source158_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source159 : Sparse := [([0, -2, 1, 0, 1, 0, 0], 18), ([0, -1, 0, 0, 1, -1, 1], -9), ([0, -1, 0, 0, 2, -1, 0], 9), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, -1, 2, -1, 0], -9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, -1, 1, 0, 1, -2, 1], 9), ([0, -1, 1, 0, 2, -2, 0], 9), ([0, -1, 1, 0, 2, -1, -1], 9), ([0, -1, 1, 1, 0, -1, 0], 9), ([0, -1, 2, -1, 1, -1, 0], 9), ([0, -1, 2, 0, 1, -1, -1], 9), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 0, 1, -1, 1, -1, 0], 9), ([1, -2, 1, 0, 1, 0, 0], 18), ([1, -1, 0, 0, 2, -1, 0], 9), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 0, 2, -1, -1], 9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, -1, 1, 1, 1, -2, 0], 9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 2, -1, 1, -1, 0], 9), ([1, -1, 2, 0, 0, -1, 0], -9), ([1, -1, 2, 0, 1, -2, 0], 9), ([1, -1, 2, 0, 1, -1, -1], 9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 1, 0, 1, -1, -1], 9)]

theorem source159_checked : normalize (row ![-1, 1, 0, 1, -1, 0] ![1, 0, 0, 0, -1, 0] (3, 3)) = source159 := by
  decide +kernel

theorem source159_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source159 (momentValues f) = 0 := by
  rw [← source159_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
