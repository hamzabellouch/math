import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source472 : Sparse := [([0, -2, 0, 0, -1, 2, 1], 9), ([0, -2, 1, 0, -1, 1, 1], -9), ([0, -1, -1, 0, -1, 2, 1], -9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, 0, -1, -1, 2, 1], 9), ([0, -1, 0, -1, 0, 1, 1], -9), ([0, -1, 0, 0, -2, 2, 1], -9), ([0, -1, 0, 0, 0, 1, 0], 9), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 1, 0, -1, 1, 0], 9), ([0, 0, 0, 0, -2, 1, 1], 9), ([0, 0, 0, 0, -1, 1, 0], -9), ([1, -2, 0, 0, 0, 1, 1], -9), ([1, -2, 0, 1, -1, 1, 1], -9), ([1, -1, -1, 0, -1, 2, 1], -9), ([1, -1, -1, 0, 0, 1, 1], -9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, 0, 0, -2, 2, 1], -9), ([1, -1, 0, 0, -1, 0, 2], -18), ([1, -1, 0, 1, -2, 1, 1], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, -1, 1, 0, -2, 1, 1], -9), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, 0, -1, -1, 1, 1], -9), ([1, 0, 0, 0, -2, 1, 1], 9), ([1, 0, 0, 0, -1, 1, 0], -9)]

theorem source472_checked : normalize (row ![-1, 0, 0, -1, 1, 1] ![0, 0, 0, 0, 1, -1] (0, -3)) = source472 := by
  decide +kernel

theorem source472_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source472 (momentValues f) = 0 := by
  rw [← source472_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source473 : Sparse := [([0, 0, 0, 1, 1, -1, -1], 9), ([0, 0, 1, 0, 1, -1, -1], 9), ([0, 1, -1, 0, 1, -1, 0], 9), ([0, 1, -1, 0, 2, -1, -1], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, -1, 2, -1, -1], 9), ([0, 1, 0, 0, 0, -1, 0], 9), ([0, 1, 0, 0, 1, 0, -2], 18), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 1, 0, 1, 1, -2, -1], 9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 2, -1, 0, 1, -1, -1], -9), ([0, 2, 0, -1, 1, -1, -1], 9), ([0, 2, 0, 0, 0, -1, -1], 9), ([0, 2, 0, 0, 1, -2, -1], 9), ([1, 0, 0, 0, 1, -1, 0], 9), ([1, 0, 0, 0, 2, -1, -1], -9), ([1, 0, 0, 1, 1, -1, -1], 9), ([1, 0, 1, 0, 1, -1, -1], 9), ([1, 1, -1, 0, 2, -1, -1], 9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 1, 0, -1, 2, -1, -1], 9), ([1, 1, 0, 0, 1, 0, -2], 18), ([1, 1, 0, 0, 2, -2, -1], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, 0, -1, -1], 9), ([1, 1, 1, 0, 1, -2, -1], 9), ([1, 2, 0, -1, 1, -1, -1], 9), ([1, 2, 0, 0, 0, -1, -1], 9)]

theorem source473_checked : normalize (row ![1, 0, 0, 1, -1, -1] ![0, 0, 0, 0, -1, 1] (3, 3)) = source473 := by
  decide +kernel

theorem source473_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source473 (momentValues f) = 0 := by
  rw [← source473_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source474 : Sparse := [([0, -1, -1, -1, 0, 2, 1], 9), ([0, -1, 0, -1, 0, 1, 1], -9), ([0, 0, -2, -1, 0, 2, 1], -9), ([0, 0, -2, 0, 0, 1, 1], 9), ([0, 0, -1, -2, 0, 2, 1], 9), ([0, 0, -1, -2, 1, 1, 1], -9), ([0, 0, -1, -1, -1, 2, 1], -9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, 0, -1, 0, 1, 0], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, -1, 0, 1, 0], -9), ([1, -1, -1, -1, 1, 1, 1], -9), ([1, -1, -1, 0, 0, 1, 1], -9), ([1, 0, -2, -1, 0, 2, 1], -9), ([1, 0, -2, -1, 1, 1, 1], -9), ([1, 0, -2, 0, 0, 1, 1], 9), ([1, 0, -1, -1, -1, 2, 1], -9), ([1, 0, -1, -1, 0, 0, 2], -18), ([1, 0, -1, 0, -1, 1, 1], -9), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, 0, -2, 0, 1, 1], -9), ([1, 0, 0, -1, -1, 1, 1], -9), ([1, 1, -2, -1, 0, 1, 1], -9), ([1, 1, -1, -2, 0, 1, 1], -9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, -1, -1, 0, 1, 0], -9)]

theorem source474_checked : normalize (row ![0, -1, -1, 0, 1, 1] ![0, 0, 0, 0, 1, -1] (0, -3)) = source474 := by
  decide +kernel

theorem source474_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source474 (momentValues f) = 0 := by
  rw [← source474_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source475 : Sparse := [([0, -1, 1, 2, 0, -1, -1], 9), ([0, -1, 2, 1, 0, -1, -1], 9), ([0, 0, 0, 1, 0, -1, 0], 9), ([0, 0, 0, 1, 1, -1, -1], 9), ([0, 0, 0, 2, 0, -1, -1], 9), ([0, 0, 1, 0, 1, -1, -1], 9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 0, 1, 1, 0, 0, -2], 18), ([0, 0, 1, 2, -1, -1, -1], -9), ([0, 0, 1, 2, 0, -2, -1], 9), ([0, 0, 2, 1, -1, -1, -1], 9), ([0, 1, 0, 1, 0, -1, -1], -9), ([0, 1, 1, 0, 0, -1, -1], 9), ([0, 1, 1, 1, -1, -1, -1], 9), ([0, 1, 1, 1, 0, -2, -1], 9), ([1, -1, 1, 1, 0, -1, 0], 9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 1, 2, 0, -1, -1], 9), ([1, -1, 2, 1, 0, -1, -1], 9), ([1, 0, 0, 1, 1, -1, -1], 9), ([1, 0, 0, 2, 0, -1, -1], 9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 1, 0, 1, -1, -1], 9), ([1, 0, 1, 1, 0, 0, -2], 18), ([1, 0, 1, 1, 1, -2, -1], 9), ([1, 0, 2, 0, 0, -1, -1], -9), ([1, 0, 2, 1, -1, -1, -1], 9), ([1, 0, 2, 1, 0, -2, -1], 9), ([1, 1, 1, 0, 0, -1, -1], 9), ([1, 1, 1, 1, -1, -1, -1], 9)]

theorem source475_checked : normalize (row ![0, 1, 1, 0, -1, -1] ![0, 0, 0, 0, -1, 1] (3, 3)) = source475 := by
  decide +kernel

theorem source475_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source475 (momentValues f) = 0 := by
  rw [← source475_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source476 : Sparse := [([0, -1, -1, 0, 0, 1, 1], 9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, 0, -2, 0, -1, 2, 1], 9), ([0, 0, -2, 0, 0, 1, 1], 9), ([0, 0, -2, 1, -1, 1, 1], -9), ([0, 0, -1, 0, -2, 2, 1], 9), ([0, 0, -1, 0, -1, 0, 2], 18), ([0, 0, -1, 1, -2, 1, 1], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, 0, -1, -1, 1, 1], 9), ([0, 0, 0, 0, -2, 1, 1], 9), ([0, 1, -2, 0, -1, 1, 1], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, -1, 0, -2, 1, 1], -9), ([0, 1, -1, 0, -1, 1, 0], 9), ([1, -1, -1, 0, -1, 2, 1], 9), ([1, -1, -1, 0, 0, 1, 1], 9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, 0, 0, -1, 1, 1], -9), ([1, 0, -2, 0, 0, 1, 1], 9), ([1, 0, -1, -1, -1, 2, 1], 9), ([1, 0, -1, -1, 0, 1, 1], -9), ([1, 0, -1, 0, -1, 0, 2], 18), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 1, -2, 1, 1], 9), ([1, 0, 0, -1, -1, 1, 1], 9), ([1, 0, 0, 0, -2, 1, 1], 9), ([1, 0, 0, 0, -1, 1, 0], 9), ([1, 1, -2, 0, -1, 1, 1], 9), ([1, 1, -1, -1, -1, 1, 1], 9)]

theorem source476_checked : normalize (row ![0, -1, 0, -1, 1, 1] ![0, 0, 0, 0, 1, -1] (3, 3)) = source476 := by
  decide +kernel

theorem source476_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source476 (momentValues f) = 0 := by
  rw [← source476_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source477 : Sparse := [([0, -1, 1, 0, 1, -1, 0], 9), ([0, -1, 1, 0, 2, -1, -1], -9), ([0, 0, 0, 0, 1, -1, 0], -9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 1, 0, 2, -2, -1], 9), ([0, 0, 1, 1, 0, -1, -1], 9), ([0, 0, 1, 1, 1, -2, -1], -9), ([0, 0, 2, -1, 1, -1, -1], -9), ([0, 0, 2, 0, 1, -2, -1], 9), ([0, 1, 0, 0, 1, -1, -1], 9), ([0, 1, 1, 0, 1, -2, -1], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, -1, 2, 0, 1, -1, -1], -9), ([1, 0, 0, 0, 1, -1, 0], -9), ([1, 0, 0, 0, 2, -1, -1], -9), ([1, 0, 0, 1, 1, -1, -1], -9), ([1, 0, 1, -1, 2, -1, -1], -9), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 1, 0, 1, 0, -2], -18), ([1, 0, 1, 1, 0, -1, -1], 9), ([1, 0, 1, 1, 1, -2, -1], -9), ([1, 0, 2, 0, 0, -1, -1], -9), ([1, 1, 0, 0, 1, -1, -1], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, 0, -1, -1], -9), ([1, 1, 1, 0, 1, -2, -1], -9)]

theorem source477_checked : normalize (row ![0, 1, 0, 1, -1, -1] ![0, 0, 0, 0, -1, 1] (0, -3)) = source477 := by
  decide +kernel

theorem source477_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source477 (momentValues f) = 0 := by
  rw [← source477_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source478 : Sparse := [([0, -1, 0, -1, 0, 1, 1], 9), ([0, -1, 0, 0, -1, 1, 1], 9), ([0, 0, -1, -1, -1, 2, 1], 9), ([0, 0, -1, -1, 0, 1, 1], 9), ([0, 0, -1, 0, -1, 1, 1], -9), ([0, 0, 0, -1, -2, 2, 1], 9), ([0, 0, 0, -1, -1, 0, 2], 18), ([0, 0, 0, 0, -2, 1, 1], 9), ([0, 0, 0, 0, -1, 1, 0], 9), ([0, 0, 1, -2, -1, 1, 1], 9), ([0, 0, 1, -1, -2, 1, 1], 9), ([0, 1, -1, -1, -1, 1, 1], 9), ([0, 1, 0, -2, -1, 1, 1], 9), ([0, 1, 0, -1, -2, 1, 1], -9), ([0, 1, 0, -1, -1, 1, 0], 9), ([1, -1, 0, -1, -1, 2, 1], 9), ([1, -1, 0, -1, 0, 1, 1], 9), ([1, -1, 0, 0, -1, 1, 1], 9), ([1, -1, 1, -1, -1, 1, 1], -9), ([1, 0, -1, -1, 0, 1, 1], 9), ([1, 0, 0, -2, -1, 2, 1], 9), ([1, 0, 0, -2, 0, 1, 1], -9), ([1, 0, 0, -1, -1, 0, 2], 18), ([1, 0, 0, -1, 0, 1, 0], 9), ([1, 0, 0, 0, -2, 1, 1], 9), ([1, 0, 1, -2, -1, 1, 1], 9), ([1, 0, 1, -1, -2, 1, 1], 9), ([1, 0, 1, -1, -1, 1, 0], 9), ([1, 1, -1, -1, -1, 1, 1], 9), ([1, 1, 0, -2, -1, 1, 1], 9)]

theorem source478_checked : normalize (row ![0, 0, -1, -1, 1, 1] ![0, 0, 0, 0, 1, -1] (3, 3)) = source478 := by
  decide +kernel

theorem source478_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source478 (momentValues f) = 0 := by
  rw [← source478_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source479 : Sparse := [([0, -1, 0, 1, 1, -1, 0], 9), ([0, -1, 0, 1, 2, -1, -1], -9), ([0, 0, -1, 1, 1, -1, 0], -9), ([0, 0, 0, 0, 1, -1, 0], 9), ([0, 0, 0, 1, 0, -1, 0], -9), ([0, 0, 0, 1, 2, -2, -1], 9), ([0, 0, 0, 2, 0, -1, -1], 9), ([0, 0, 0, 2, 1, -2, -1], -9), ([0, 0, 1, 0, 1, -1, -1], -9), ([0, 0, 1, 1, 1, -2, -1], 9), ([0, 1, -1, 1, 1, -1, -1], 9), ([0, 1, 0, 1, 1, -2, -1], -9), ([1, -1, 0, 2, 1, -1, -1], -9), ([1, -1, 1, 1, 1, -1, -1], -9), ([1, 0, -1, 1, 1, -1, 0], -9), ([1, 0, -1, 1, 2, -1, -1], -9), ([1, 0, -1, 2, 1, -1, -1], -9), ([1, 0, 0, 0, 2, -1, -1], -9), ([1, 0, 0, 1, 0, -1, 0], -9), ([1, 0, 0, 1, 1, 0, -2], -18), ([1, 0, 0, 2, 0, -1, -1], 9), ([1, 0, 0, 2, 1, -2, -1], -9), ([1, 0, 1, 1, 0, -1, -1], -9), ([1, 1, -1, 1, 1, -1, -1], 9), ([1, 1, 0, 0, 1, -1, -1], -9), ([1, 1, 0, 1, 0, -1, -1], -9), ([1, 1, 0, 1, 1, -2, -1], -9)]

theorem source479_checked : normalize (row ![0, 0, 1, 1, -1, -1] ![0, 0, 0, 0, -1, 1] (0, -3)) = source479 := by
  decide +kernel

theorem source479_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source479 (momentValues f) = 0 := by
  rw [← source479_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
