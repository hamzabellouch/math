import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source16 : Sparse := [([0, -1, 0, 0, 2, -2, 1], 18), ([0, -1, 0, 0, 2, -1, 0], 18), ([0, -1, 0, 1, 2, -2, 0], -18), ([0, -1, 1, 0, 2, -2, 0], 18), ([0, 0, -1, 0, 2, -2, 1], -18), ([0, 0, -1, 0, 2, -1, 0], 18), ([0, 0, -1, 1, 2, -2, 0], 18), ([0, 0, 0, -1, 2, -2, 1], 18), ([0, 0, 0, 0, 1, -2, 1], 18), ([0, 0, 0, 0, 3, -3, 0], 36), ([0, 0, 0, 1, 1, -2, 0], 18), ([0, 0, 0, 1, 2, -2, -1], 18), ([0, 0, 1, 0, 2, -2, -1], 18), ([0, 1, -1, 0, 2, -2, 0], 18), ([0, 1, 0, -1, 2, -2, 0], 18), ([1, -1, 0, 0, 2, -1, 0], 18), ([1, -1, 0, 1, 2, -2, 0], -18), ([1, 0, -1, 0, 2, -2, 1], -18), ([1, 0, -1, 0, 2, -1, 0], 18), ([1, 0, 0, -1, 2, -1, 0], -18), ([1, 0, 0, 0, 1, -2, 1], 18), ([1, 0, 0, 0, 2, -1, -1], -18), ([1, 0, 0, 1, 1, -2, 0], 18), ([1, 0, 1, -1, 2, -2, 0], 18), ([1, 0, 1, 0, 1, -2, 0], -18), ([1, 1, 0, 0, 1, -2, 0], -18), ([1, 1, 0, 0, 2, -2, -1], 18)]

theorem source16_checked : normalize (row ![0, 0, 0, 2, -2, 0] ![0, 0, 0, 2, -2, 0] (6, 0)) = source16 := by
  decide +kernel

theorem source16_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source16 (momentValues f) = 0 := by
  rw [← source16_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source17 : Sparse := [([0, -1, 0, 0, 2, 1, -2], 18), ([0, -1, 0, 1, 2, 0, -2], 18), ([0, 0, -1, 0, 2, 0, -1], 18), ([0, 0, -1, 0, 2, 1, -2], -18), ([0, 0, -1, 1, 2, 0, -2], 18), ([0, 0, 0, -1, 2, 0, -1], 18), ([0, 0, 0, -1, 2, 1, -2], 18), ([0, 0, 0, 0, 1, 1, -2], 18), ([0, 0, 0, 0, 3, 0, -3], 36), ([0, 0, 1, -1, 2, 0, -2], 18), ([0, 0, 1, 0, 2, -1, -2], 18), ([0, 1, -1, 0, 2, 0, -2], 18), ([0, 1, 0, -1, 2, 0, -2], -18), ([0, 1, 0, 0, 1, 0, -2], 18), ([0, 1, 0, 0, 2, -1, -2], 18), ([1, -1, 0, 0, 2, 0, -1], -18), ([1, -1, 1, 0, 2, 0, -2], 18), ([1, 0, -1, 0, 2, 0, -1], 18), ([1, 0, -1, 0, 2, 1, -2], -18), ([1, 0, 0, -1, 2, 0, -1], 18), ([1, 0, 0, 0, 1, 1, -2], 18), ([1, 0, 0, 0, 2, -1, -1], -18), ([1, 0, 0, 1, 1, 0, -2], -18), ([1, 0, 0, 1, 2, -1, -2], 18), ([1, 0, 1, 0, 1, 0, -2], -18), ([1, 1, 0, -1, 2, 0, -2], -18), ([1, 1, 0, 0, 1, 0, -2], 18)]

theorem source17_checked : normalize (row ![0, 0, 0, 2, 0, -2] ![0, 0, 0, 2, 0, -2] (6, 0)) = source17 := by
  decide +kernel

theorem source17_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source17 (momentValues f) = 0 := by
  rw [← source17_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source18 : Sparse := [([0, -1, 0, 2, -2, 0, 1], 18), ([0, -1, 0, 2, -2, 1, 0], 18), ([0, -1, 0, 2, -1, 0, 0], 18), ([0, -1, 1, 2, -2, 0, 0], -18), ([0, 0, -1, 2, -2, 1, 0], 18), ([0, 0, 0, 1, -2, 1, 0], 18), ([0, 0, 0, 2, -2, -1, 1], 18), ([0, 0, 0, 2, -2, 1, -1], -18), ([0, 0, 0, 2, -1, 0, -1], 18), ([0, 0, 0, 3, -3, 0, 0], 36), ([0, 0, 1, 1, -2, 0, 0], 18), ([0, 0, 1, 2, -2, -1, 0], 18), ([0, 0, 1, 2, -2, 0, -1], 18), ([0, 1, -1, 2, -2, 0, 0], 18), ([0, 1, 0, 2, -2, 0, -1], 18), ([1, -1, 0, 2, -1, 0, 0], 18), ([1, -1, 1, 2, -2, 0, 0], -18), ([1, 0, -1, 2, -2, 0, 1], 18), ([1, 0, -1, 2, -1, 0, 0], -18), ([1, 0, 0, 1, -2, 0, 1], -18), ([1, 0, 0, 1, -2, 1, 0], 18), ([1, 0, 0, 2, -2, 1, -1], -18), ([1, 0, 0, 2, -1, -1, 0], -18), ([1, 0, 0, 2, -1, 0, -1], 18), ([1, 0, 1, 1, -2, 0, 0], 18), ([1, 1, 0, 1, -2, 0, 0], -18), ([1, 1, 0, 2, -2, -1, 0], 18)]

theorem source18_checked : normalize (row ![0, 0, 2, -2, 0, 0] ![0, 0, 2, -2, 0, 0] (6, 0)) = source18 := by
  decide +kernel

theorem source18_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source18 (momentValues f) = 0 := by
  rw [← source18_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source19 : Sparse := [([0, -1, 0, 2, 1, -2, 0], 18), ([0, -1, 1, 2, 0, -2, 0], 18), ([0, 0, -1, 2, 0, -2, 1], 18), ([0, 0, -1, 2, 0, -1, 0], 18), ([0, 0, -1, 2, 1, -2, 0], 18), ([0, 0, 0, 1, 1, -2, 0], 18), ([0, 0, 0, 2, -1, -2, 1], 18), ([0, 0, 0, 2, 0, -1, -1], 18), ([0, 0, 0, 2, 1, -2, -1], -18), ([0, 0, 0, 3, 0, -3, 0], 36), ([0, 0, 1, 2, 0, -2, -1], 18), ([0, 1, -1, 2, 0, -2, 0], -18), ([0, 1, 0, 1, 0, -2, 0], 18), ([0, 1, 0, 2, -1, -2, 0], 18), ([0, 1, 0, 2, 0, -2, -1], 18), ([1, -1, 0, 2, 0, -2, 1], 18), ([1, -1, 0, 2, 0, -1, 0], -18), ([1, 0, -1, 2, 0, -1, 0], 18), ([1, 0, 0, 1, 0, -2, 1], -18), ([1, 0, 0, 1, 1, -2, 0], 18), ([1, 0, 0, 2, -1, -1, 0], -18), ([1, 0, 0, 2, 0, -1, -1], 18), ([1, 0, 0, 2, 1, -2, -1], -18), ([1, 0, 1, 1, 0, -2, 0], -18), ([1, 0, 1, 2, -1, -2, 0], 18), ([1, 1, -1, 2, 0, -2, 0], -18), ([1, 1, 0, 1, 0, -2, 0], 18)]

theorem source19_checked : normalize (row ![0, 0, 2, 0, -2, 0] ![0, 0, 2, 0, -2, 0] (6, 0)) = source19 := by
  decide +kernel

theorem source19_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source19 (momentValues f) = 0 := by
  rw [← source19_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source20 : Sparse := [([0, -1, 0, 2, 1, 0, -2], 18), ([0, -1, 1, 2, 0, 0, -2], 18), ([0, 0, -1, 2, 0, 1, -2], 18), ([0, 0, 0, 2, -1, 0, -1], 18), ([0, 0, 0, 2, -1, 1, -2], 18), ([0, 0, 0, 2, 0, -1, -1], 18), ([0, 0, 0, 2, 1, -1, -2], 18), ([0, 0, 0, 3, 0, 0, -3], 36), ([0, 0, 1, 1, 0, 0, -2], 18), ([0, 0, 1, 2, -1, 0, -2], 18), ([0, 0, 1, 2, 0, -1, -2], -18), ([0, 1, -1, 2, 0, 0, -2], 18), ([0, 1, 0, 1, 0, 0, -2], 18), ([0, 1, 0, 2, -1, 0, -2], -18), ([0, 1, 0, 2, 0, -1, -2], 18), ([1, -1, 0, 2, 0, 0, -1], -18), ([1, -1, 0, 2, 0, 1, -2], 18), ([1, 0, -1, 2, 0, 0, -1], -18), ([1, 0, -1, 2, 1, 0, -2], 18), ([1, 0, 0, 1, 0, 1, -2], -18), ([1, 0, 0, 1, 1, 0, -2], -18), ([1, 0, 0, 2, -1, 0, -1], 18), ([1, 0, 0, 2, 0, -1, -1], 18), ([1, 0, 1, 1, 0, 0, -2], 18), ([1, 0, 1, 2, 0, -1, -2], -18), ([1, 1, 0, 1, 0, 0, -2], 18), ([1, 1, 0, 2, -1, 0, -2], -18)]

theorem source20_checked : normalize (row ![0, 0, 2, 0, 0, -2] ![0, 0, 2, 0, 0, -2] (6, 0)) = source20 := by
  decide +kernel

theorem source20_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source20 (momentValues f) = 0 := by
  rw [← source20_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source21 : Sparse := [([0, -1, 2, -2, 0, 0, 1], -18), ([0, -1, 2, -2, 0, 1, 0], 18), ([0, -1, 2, -2, 1, 0, 0], 18), ([0, -1, 2, -1, 0, 0, 0], 18), ([0, 0, 1, -2, 0, 0, 1], 18), ([0, 0, 1, -2, 1, 0, 0], 18), ([0, 0, 2, -2, -1, 0, 1], 18), ([0, 0, 2, -2, -1, 1, 0], 18), ([0, 0, 2, -2, 0, -1, 1], 18), ([0, 0, 2, -2, 1, -1, 0], -18), ([0, 0, 2, -2, 1, 0, -1], 18), ([0, 0, 2, -1, 0, -1, 0], 18), ([0, 0, 3, -3, 0, 0, 0], 36), ([0, 1, 2, -2, 0, -1, 0], 18), ([0, 1, 2, -2, 0, 0, -1], 18), ([1, -1, 2, -2, 0, 0, 1], -18), ([1, -1, 2, -1, 0, 0, 0], 18), ([1, 0, 1, -2, 0, 0, 1], 18), ([1, 0, 1, -2, 0, 1, 0], -18), ([1, 0, 1, -2, 1, 0, 0], 18), ([1, 0, 2, -2, 0, 1, -1], 18), ([1, 0, 2, -2, 1, -1, 0], -18), ([1, 0, 2, -1, -1, 0, 0], -18), ([1, 0, 2, -1, 0, -1, 0], 18), ([1, 0, 2, -1, 0, 0, -1], -18), ([1, 1, 1, -2, 0, 0, 0], -18), ([1, 1, 2, -2, -1, 0, 0], 18)]

theorem source21_checked : normalize (row ![0, 2, -2, 0, 0, 0] ![0, 2, -2, 0, 0, 0] (6, 0)) = source21 := by
  decide +kernel

theorem source21_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source21 (momentValues f) = 0 := by
  rw [← source21_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source22 : Sparse := [([0, -1, 2, 0, -2, 0, 1], 18), ([0, -1, 2, 1, -2, 0, 0], 18), ([0, 0, 1, 1, -2, 0, 0], 18), ([0, 0, 2, -1, -2, 1, 0], 18), ([0, 0, 2, 0, -2, -1, 1], 18), ([0, 0, 2, 0, -2, 1, -1], 18), ([0, 0, 2, 0, -1, -1, 0], 18), ([0, 0, 2, 0, -1, 0, -1], 18), ([0, 0, 2, 1, -2, -1, 0], -18), ([0, 0, 2, 1, -2, 0, -1], 18), ([0, 0, 3, 0, -3, 0, 0], 36), ([0, 1, 1, 0, -2, 0, 0], 18), ([0, 1, 2, -1, -2, 0, 0], 18), ([0, 1, 2, 0, -2, -1, 0], 18), ([0, 1, 2, 0, -2, 0, -1], -18), ([1, -1, 2, 0, -2, 1, 0], 18), ([1, -1, 2, 0, -1, 0, 0], -18), ([1, 0, 1, 0, -2, 0, 1], -18), ([1, 0, 1, 0, -2, 1, 0], -18), ([1, 0, 1, 1, -2, 0, 0], 18), ([1, 0, 2, -1, -2, 0, 1], 18), ([1, 0, 2, -1, -1, 0, 0], -18), ([1, 0, 2, 0, -1, -1, 0], 18), ([1, 0, 2, 0, -1, 0, -1], 18), ([1, 0, 2, 1, -2, -1, 0], -18), ([1, 1, 1, 0, -2, 0, 0], 18), ([1, 1, 2, 0, -2, 0, -1], -18)]

theorem source22_checked : normalize (row ![0, 2, 0, -2, 0, 0] ![0, 2, 0, -2, 0, 0] (6, 0)) = source22 := by
  decide +kernel

theorem source22_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source22 (momentValues f) = 0 := by
  rw [← source22_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source23 : Sparse := [([0, -1, 2, 0, 0, -2, 1], 18), ([0, -1, 2, 1, 0, -2, 0], 18), ([0, 0, 1, 0, 0, -2, 1], 18), ([0, 0, 2, -1, 0, -2, 1], 18), ([0, 0, 2, -1, 0, -1, 0], 18), ([0, 0, 2, -1, 1, -2, 0], 18), ([0, 0, 2, 0, -1, -2, 1], -18), ([0, 0, 2, 0, -1, -1, 0], 18), ([0, 0, 2, 0, 1, -2, -1], 18), ([0, 0, 2, 1, -1, -2, 0], 18), ([0, 0, 3, 0, 0, -3, 0], 36), ([0, 1, 1, 0, 0, -2, 0], 18), ([0, 1, 2, -1, 0, -2, 0], -18), ([0, 1, 2, 0, -1, -2, 0], 18), ([0, 1, 2, 0, 0, -2, -1], 18), ([1, -1, 2, 0, 0, -1, 0], -18), ([1, -1, 2, 0, 1, -2, 0], 18), ([1, 0, 1, 0, 0, -2, 1], 18), ([1, 0, 1, 0, 1, -2, 0], -18), ([1, 0, 1, 1, 0, -2, 0], -18), ([1, 0, 2, -1, 0, -1, 0], 18), ([1, 0, 2, 0, -1, -2, 1], -18), ([1, 0, 2, 0, -1, -1, 0], 18), ([1, 0, 2, 0, 0, -1, -1], -18), ([1, 0, 2, 1, 0, -2, -1], 18), ([1, 1, 1, 0, 0, -2, 0], 18), ([1, 1, 2, -1, 0, -2, 0], -18)]

theorem source23_checked : normalize (row ![0, 2, 0, 0, -2, 0] ![0, 2, 0, 0, -2, 0] (6, 0)) = source23 := by
  decide +kernel

theorem source23_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source23 (momentValues f) = 0 := by
  rw [← source23_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
