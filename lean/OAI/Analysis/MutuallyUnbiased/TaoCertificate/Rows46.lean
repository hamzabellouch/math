import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source368 : Sparse := [([0, 0, 0, -1, 0, 2, -1], 18), ([0, 1, -1, -1, 0, 1, 0], -9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, 0, -2, 0, 1, 0], 9), ([0, 1, 0, -2, 1, 1, -1], -9), ([0, 1, 0, -1, -1, 1, 0], 9), ([0, 1, 0, -1, 0, 0, 0], 9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 1, 0, -1, 1, 1, -2], 9), ([0, 1, 0, 0, -1, 1, -1], 9), ([0, 1, 1, -2, 0, 1, -1], 9), ([0, 1, 1, -1, 0, 1, -2], 9), ([0, 2, -1, -1, 0, 1, -1], 9), ([0, 2, 0, -2, 0, 1, -1], 9), ([1, 0, 0, -1, 0, 2, -1], 18), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, 0, 1, -1], 9), ([1, 1, 0, -2, 0, 1, 0], 9), ([1, 1, 0, -1, -1, 1, 0], 9), ([1, 1, 0, -1, 1, 1, -2], 9), ([1, 1, 0, 0, -1, 1, -1], 9), ([1, 1, 0, 0, 0, 0, -1], 9), ([1, 1, 0, 0, 0, 1, -2], -9), ([1, 1, 1, -2, 0, 1, -1], 9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, -1, 0, 1, -2], 9), ([1, 2, 0, -1, -1, 1, -1], 9), ([1, 2, 0, -1, 0, 1, -2], 9)]

theorem source368_checked : normalize (row ![1, 0, -1, 0, 1, -1] ![1, 0, 0, 0, -1, 0] (3, 3)) = source368 := by
  decide +kernel

theorem source368_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source368 (momentValues f) = 0 := by
  rw [← source368_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source369 : Sparse := [([0, -2, 0, 1, 0, -1, 2], -9), ([0, -2, 0, 1, 1, -1, 1], -9), ([0, -2, 0, 2, 0, -1, 1], 9), ([0, -2, 1, 1, 0, -1, 1], 9), ([0, -1, -1, 1, 0, 0, 1], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, 0, 0, 0, -1, 2], 9), ([0, -1, 0, 0, 0, 0, 1], -9), ([0, -1, 0, 1, -1, 0, 1], 9), ([0, -1, 0, 1, 0, 0, 0], 9), ([0, -1, 0, 2, -1, -1, 1], -9), ([0, -1, 1, 1, 0, -1, 0], -9), ([1, -2, 0, 1, 0, -1, 2], -9), ([1, -2, 0, 1, 1, -1, 1], -9), ([1, -1, -1, 1, 0, -1, 2], -9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 2, 0, -1, 1], -9), ([1, -1, 0, 0, 0, -1, 2], 9), ([1, -1, 0, 0, 0, 0, 1], -9), ([1, -1, 0, 0, 1, -1, 1], -9), ([1, -1, 0, 1, -1, -1, 2], -9), ([1, -1, 0, 1, 1, -1, 0], -9), ([1, -1, 0, 2, 0, -1, 0], -9), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, 0, 0, 1, 0, -2, 1], -18)]

theorem source369_checked : normalize (row ![-1, 0, 1, 0, -1, 1] ![-1, 0, 0, 0, 1, 0] (0, -3)) = source369 := by
  decide +kernel

theorem source369_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source369 (momentValues f) = 0 := by
  rw [← source369_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source370 : Sparse := [([0, 1, -1, 0, -1, 1, 0], 9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 1, 0, 0, -1, 0, 0], -9), ([0, 1, 0, 0, 0, 0, -1], -9), ([0, 1, 0, 1, -1, 0, -1], 9), ([0, 1, 0, 1, -1, 1, -2], -9), ([0, 1, 1, 0, -2, 1, -1], -9), ([0, 1, 1, 0, -1, 0, -1], 9), ([0, 2, -1, 0, -1, 1, -1], -9), ([0, 2, 0, -1, -1, 1, -1], -9), ([0, 2, 0, 0, -2, 1, -1], 9), ([0, 2, 0, 0, -1, 1, -2], 9), ([1, 0, 0, 0, -1, 2, -1], -18), ([1, 1, -1, 0, -1, 1, 0], 9), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, 0, -1, -1, 1, 0], -9), ([1, 1, 0, -1, 0, 1, -1], 9), ([1, 1, 0, 0, -2, 1, 0], -9), ([1, 1, 0, 0, -1, 0, 0], -9), ([1, 1, 0, 0, 0, 0, -1], -9), ([1, 1, 0, 0, 0, 1, -2], -9), ([1, 1, 0, 1, -2, 1, -1], -9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, 0, -1, 1, -2], -9), ([1, 2, -1, 0, -1, 1, -1], -9), ([1, 2, 0, -1, -1, 1, -1], -9)]

theorem source370_checked : normalize (row ![1, 0, 0, -1, 1, -1] ![1, 0, 0, 0, -1, 0] (0, -3)) = source370 := by
  decide +kernel

theorem source370_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source370 (momentValues f) = 0 := by
  rw [← source370_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source371 : Sparse := [([0, -2, 0, 0, 1, -1, 2], 9), ([0, -2, 0, 0, 2, -1, 1], 9), ([0, -1, -1, 0, 1, -1, 2], 9), ([0, -1, -1, 0, 1, 0, 1], 9), ([0, -1, -1, 0, 2, -1, 1], -9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, 0, -1, 1, -1, 2], -9), ([0, -1, 0, -1, 1, 0, 1], 9), ([0, -1, 0, -1, 2, -1, 1], 9), ([0, -1, 0, 0, 0, -1, 2], 9), ([0, -1, 0, 0, 2, -1, 0], 9), ([0, -1, 0, 1, 1, -1, 0], 9), ([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, 0, 0, 0, 1, -2, 1], 18), ([1, -2, 0, 1, 1, -1, 1], 9), ([1, -2, 1, 0, 1, -1, 1], 9), ([1, -1, -1, 0, 1, -1, 2], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, 0, -1, 2, -1, 1], 9), ([1, -1, 0, 0, 0, -1, 2], 9), ([1, -1, 0, 0, 0, 0, 1], 9), ([1, -1, 0, 0, 1, 0, 0], 9), ([1, -1, 0, 0, 2, -1, 0], 9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 0, 1, 1, -1, 0], 9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 1, 0, 1, -1, 0], -9), ([1, 0, 0, 0, 1, -2, 1], 18)]

theorem source371_checked : normalize (row ![-1, 0, 0, 1, -1, 1] ![-1, 0, 0, 0, 1, 0] (3, 3)) = source371 := by
  decide +kernel

theorem source371_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source371 (momentValues f) = 0 := by
  rw [← source371_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source372 : Sparse := [([0, -2, 1, 0, 0, 1, 0], 9), ([0, -2, 2, -1, 0, 1, 0], -9), ([0, -1, 1, -2, 0, 1, 1], -9), ([0, -1, 1, -1, 0, 0, 1], 9), ([0, -1, 1, -1, 1, 0, 0], -9), ([0, -1, 1, -1, 1, 1, -1], 9), ([0, -1, 1, 0, 0, 0, 0], -9), ([0, -1, 2, -2, 0, 1, 0], 9), ([0, -1, 2, -1, -1, 1, 0], 9), ([0, -1, 2, -1, 0, 1, -1], -9), ([0, 0, 1, -1, -1, 1, 0], -9), ([0, 0, 1, -1, 0, 0, 0], 9), ([1, -2, 1, -1, 0, 1, 1], -9), ([1, -2, 1, -1, 1, 1, 0], -9), ([1, -2, 1, 0, 0, 1, 0], 9), ([1, -2, 2, -1, 0, 1, 0], -9), ([1, -1, 0, -1, 0, 2, 0], -18), ([1, -1, 1, -2, 1, 1, 0], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 1, 0, 0], -9), ([1, -1, 1, -1, 1, 1, -1], 9), ([1, -1, 1, 0, -1, 1, 0], -9), ([1, -1, 1, 0, 0, 0, 0], -9), ([1, -1, 1, 0, 0, 1, -1], -9), ([1, -1, 2, -1, 0, 1, -1], -9), ([1, 0, 1, -2, 0, 1, 0], -9), ([1, 0, 1, -1, 0, 1, -1], -9)]

theorem source372_checked : normalize (row ![-1, 1, -1, 0, 1, 0] ![0, 1, 0, 0, -1, 0] (0, -3)) = source372 := by
  decide +kernel

theorem source372_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source372 (momentValues f) = 0 := by
  rw [← source372_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source373 : Sparse := [([0, 0, -1, 1, 0, -1, 1], 9), ([0, 0, -1, 1, 0, 0, 0], 9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, -1, 2, 0, -1, 0], 9), ([0, 1, -2, 1, 1, -1, 0], 9), ([0, 1, -2, 2, 0, -1, 0], 9), ([0, 1, -1, 0, 0, -1, 1], 9), ([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, -1, 1, 0, 0, -1], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, -1, 2, -1, -1, 0], 9), ([0, 1, -1, 2, 0, -1, -1], -9), ([0, 1, 0, 1, 0, -2, 0], 18), ([0, 2, -1, 1, -1, -1, 0], 9), ([0, 2, -1, 1, 0, -1, -1], 9), ([1, 0, -1, 1, 0, -1, 1], 9), ([1, 0, -1, 2, 0, -1, 0], 9), ([1, 1, -2, 1, 0, -1, 1], 9), ([1, 1, -1, 0, 0, -1, 1], 9), ([1, 1, -1, 0, 0, 0, 0], 9), ([1, 1, -1, 0, 1, -1, 0], 9), ([1, 1, -1, 1, -1, -1, 1], -9), ([1, 1, -1, 1, -1, 0, 0], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, -1, 2, -1, -1, 0], 9), ([1, 1, 0, 1, 0, -2, 0], 18), ([1, 2, -2, 1, 0, -1, 0], 9), ([1, 2, -1, 0, 0, -1, 0], -9), ([1, 2, -1, 1, -1, -1, 0], 9), ([1, 2, -1, 1, 0, -1, -1], 9)]

theorem source373_checked : normalize (row ![1, -1, 1, 0, -1, 0] ![0, -1, 0, 0, 1, 0] (3, 3)) = source373 := by
  decide +kernel

theorem source373_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source373 (momentValues f) = 0 := by
  rw [← source373_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source374 : Sparse := [([0, -2, 1, 0, -1, 1, 1], 9), ([0, -2, 1, 0, 0, 1, 0], 9), ([0, -2, 1, 1, -1, 1, 0], -9), ([0, -2, 2, 0, -1, 1, 0], 9), ([0, -1, 0, 0, -1, 2, 0], 18), ([0, -1, 1, -1, 0, 1, 0], 9), ([0, -1, 1, 0, -2, 1, 1], 9), ([0, -1, 1, 0, 0, 0, 0], 9), ([0, -1, 1, 0, 0, 1, -1], -9), ([0, -1, 1, 1, -2, 1, 0], 9), ([0, -1, 1, 1, -1, 0, 0], 9), ([0, -1, 1, 1, -1, 1, -1], 9), ([0, -1, 2, 0, -1, 1, -1], 9), ([0, 0, 1, -1, -1, 1, 0], 9), ([0, 0, 1, 0, -1, 1, -1], 9), ([1, -2, 1, 0, -1, 1, 1], 9), ([1, -2, 1, 0, 0, 1, 0], 9), ([1, -1, 0, 0, -1, 2, 0], 18), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, -1, 0, 1, 0], 9), ([1, -1, 1, 0, -2, 1, 1], 9), ([1, -1, 1, 0, -1, 0, 1], 9), ([1, -1, 1, 1, -2, 1, 0], 9), ([1, -1, 1, 1, -1, 1, -1], 9), ([1, -1, 2, -1, -1, 1, 0], 9), ([1, -1, 2, 0, -2, 1, 0], 9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 0, 1, 0, -2, 1, 0], -9), ([1, 0, 1, 0, -1, 0, 0], 9), ([1, 0, 1, 0, -1, 1, -1], 9)]

theorem source374_checked : normalize (row ![-1, 1, 0, -1, 1, 0] ![0, 1, 0, 0, -1, 0] (3, 3)) = source374 := by
  decide +kernel

theorem source374_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source374 (momentValues f) = 0 := by
  rw [← source374_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source375 : Sparse := [([0, 0, -1, 0, 1, 0, 0], -9), ([0, 0, -1, 0, 2, -1, 0], 9), ([0, 1, -2, 0, 1, -1, 1], 9), ([0, 1, -2, 0, 2, -1, 0], -9), ([0, 1, -2, 1, 1, -1, 0], -9), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, -1, 0, 0, -1, 1], -9), ([0, 1, -1, 0, 0, 0, 0], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 2, -2, 0, 1, -1, 0], 9), ([0, 2, -1, -1, 1, -1, 0], -9), ([1, 0, -1, 0, 1, -1, 1], -9), ([1, 0, -1, 0, 1, 0, 0], -9), ([1, 0, -1, 0, 2, -1, 0], 9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 1, -2, 0, 2, -1, 0], -9), ([1, 1, -2, 1, 1, -1, 0], -9), ([1, 1, -1, -1, 1, -1, 1], -9), ([1, 1, -1, -1, 2, -1, 0], -9), ([1, 1, -1, 0, 1, 0, -1], -9), ([1, 1, -1, 0, 2, -1, -1], -9), ([1, 1, -1, 1, 0, -1, 0], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, 0, 1, -2, 0], -18), ([1, 2, -1, 0, 0, -1, 0], -9), ([1, 2, -1, 0, 1, -1, -1], -9)]

theorem source375_checked : normalize (row ![1, -1, 0, 1, -1, 0] ![0, -1, 0, 0, 1, 0] (0, -3)) = source375 := by
  decide +kernel

theorem source375_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source375 (momentValues f) = 0 := by
  rw [← source375_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
