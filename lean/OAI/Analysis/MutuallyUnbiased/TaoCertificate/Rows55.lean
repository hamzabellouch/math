import OAI.Analysis.MutuallyUnbiased.Tao.TaoSparse

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def source440 : Sparse := [([0, -1, 1, -1, 1, -1, 1], 9), ([0, -1, 1, 0, 0, -1, 1], 9), ([0, 0, 0, -1, 0, -1, 2], 18), ([0, 0, 1, -2, 0, 0, 1], 9), ([0, 0, 1, -2, 1, -1, 1], 9), ([0, 0, 1, -1, -1, 0, 1], 9), ([0, 0, 1, -1, 1, -2, 1], -9), ([0, 0, 1, -1, 1, -1, 0], 9), ([0, 0, 1, 0, 0, -2, 1], 9), ([0, 0, 2, -2, 0, -1, 1], 9), ([0, 0, 2, -1, 0, -2, 1], 9), ([0, 1, 1, -2, 0, -1, 1], -9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, -1, 0, -2, 1], 9), ([0, 1, 1, -1, 0, -1, 0], 9), ([1, -1, 1, -1, 0, 0, 1], -9), ([1, -1, 1, -1, 1, -1, 1], 9), ([1, -1, 1, 0, 0, -1, 1], 9), ([1, -1, 2, -1, 0, -1, 1], 9), ([1, 0, 0, -1, 0, -1, 2], 18), ([1, 0, 1, -2, 0, 0, 1], 9), ([1, 0, 1, -2, 1, -1, 1], 9), ([1, 0, 1, -1, -1, 0, 1], 9), ([1, 0, 1, -1, 0, 0, 0], 9), ([1, 0, 1, 0, -1, -1, 1], -9), ([1, 0, 1, 0, 0, -2, 1], 9), ([1, 0, 1, 0, 0, -1, 0], 9), ([1, 0, 2, -1, -1, -1, 1], 9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, -1, 0, -2, 1], 9)]

theorem source440_checked : normalize (row ![0, 1, -1, 0, -1, 1] ![0, 1, 0, 0, 0, -1] (3, 3)) = source440 := by
  decide +kernel

theorem source440_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source440 (momentValues f) = 0 := by
  rw [← source440_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source441 : Sparse := [([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, -1, 2, 0, 1, -1], -9), ([0, 0, -2, 1, 0, 2, -1], 9), ([0, 0, -2, 1, 1, 1, -1], -9), ([0, 0, -2, 2, 0, 1, -1], 9), ([0, 0, -1, 0, 0, 1, 0], -9), ([0, 0, -1, 0, 1, 1, -1], 9), ([0, 0, -1, 1, -1, 1, 0], 9), ([0, 0, -1, 1, -1, 2, -1], -9), ([0, 0, -1, 1, 0, 0, 0], -9), ([0, 1, -2, 1, 0, 1, -1], -9), ([0, 1, -1, 1, 0, 0, -1], 9), ([1, -1, -1, 1, 0, 2, -1], -9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, 0, -2, 1, 1, 1, -1], -9), ([1, 0, -1, 0, 0, 1, 0], -9), ([1, 0, -1, 0, 0, 2, -1], -9), ([1, 0, -1, 0, 1, 1, -1], 9), ([1, 0, -1, 1, 0, 0, 0], -9), ([1, 0, -1, 1, 1, 0, -1], -9), ([1, 0, -1, 2, -1, 1, -1], -9), ([1, 0, -1, 2, 0, 0, -1], -9), ([1, 0, 0, 1, 0, 1, -2], -18), ([1, 1, -2, 1, 0, 1, -1], -9), ([1, 1, -1, 0, 0, 1, -1], -9), ([1, 1, -1, 1, -1, 1, -1], -9), ([1, 1, -1, 1, 0, 0, -1], 9)]

theorem source441_checked : normalize (row ![0, -1, 1, 0, 1, -1] ![0, -1, 0, 0, 0, 1] (0, -3)) = source441 := by
  decide +kernel

theorem source441_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source441 (momentValues f) = 0 := by
  rw [← source441_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source442 : Sparse := [([0, -1, 1, 0, -1, 0, 1], -9), ([0, -1, 2, 0, -1, -1, 1], 9), ([0, 0, 1, 0, -1, 0, 0], 9), ([0, 0, 1, 0, 0, -2, 1], 9), ([0, 0, 1, 0, 0, -1, 0], -9), ([0, 0, 1, 1, -2, -1, 1], -9), ([0, 0, 1, 1, -1, -1, 0], 9), ([0, 0, 2, -1, -1, -1, 1], -9), ([0, 0, 2, 0, -2, -1, 1], 9), ([0, 0, 2, 0, -1, -2, 1], -9), ([0, 1, 1, -1, -1, -1, 1], 9), ([0, 1, 1, 0, -1, -1, 0], -9), ([1, -1, 1, 0, 0, -1, 1], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, 0, 0, 0, -1, -1, 2], -18), ([1, 0, 1, -1, -1, 0, 1], -9), ([1, 0, 1, -1, 0, -1, 1], -9), ([1, 0, 1, 0, -2, 0, 1], -9), ([1, 0, 1, 0, 0, -2, 1], 9), ([1, 0, 1, 0, 0, -1, 0], -9), ([1, 0, 1, 1, -1, -2, 1], -9), ([1, 0, 2, -1, -1, -1, 1], -9), ([1, 0, 2, 0, -1, -2, 1], -9), ([1, 1, 1, -1, -1, -1, 1], 9), ([1, 1, 1, 0, -2, -1, 1], -9), ([1, 1, 1, 0, -1, -2, 1], -9), ([1, 1, 1, 0, -1, -1, 0], -9)]

theorem source442_checked : normalize (row ![0, 1, 0, -1, -1, 1] ![0, 1, 0, 0, 0, -1] (0, -3)) = source442 := by
  decide +kernel

theorem source442_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source442 (momentValues f) = 0 := by
  rw [← source442_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source443 : Sparse := [([0, -1, -1, 0, 1, 2, -1], 9), ([0, -1, -1, 0, 2, 1, -1], 9), ([0, 0, -2, 0, 2, 1, -1], 9), ([0, 0, -1, -1, 1, 1, 0], 9), ([0, 0, -1, -1, 1, 2, -1], 9), ([0, 0, -1, -1, 2, 1, -1], -9), ([0, 0, -1, 0, 1, 0, 0], 9), ([0, 0, -1, 0, 2, 0, -1], 9), ([0, 0, -1, 1, 0, 1, -1], 9), ([0, 0, -1, 1, 1, 0, -1], 9), ([0, 0, 0, 0, 1, 1, -2], 18), ([0, 1, -2, 0, 1, 1, -1], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, 0, 0, 1, -1], 9), ([0, 1, -1, 0, 1, 0, -1], -9), ([1, -1, -1, 0, 1, 1, 0], 9), ([1, -1, -1, 0, 1, 2, -1], 9), ([1, -1, -1, 0, 2, 1, -1], 9), ([1, -1, -1, 1, 1, 1, -1], -9), ([1, 0, -2, 0, 1, 2, -1], 9), ([1, 0, -2, 1, 1, 1, -1], 9), ([1, 0, -1, -1, 1, 2, -1], 9), ([1, 0, -1, 0, 0, 1, 0], 9), ([1, 0, -1, 0, 0, 2, -1], -9), ([1, 0, -1, 0, 2, 0, -1], 9), ([1, 0, -1, 1, 0, 1, -1], 9), ([1, 0, -1, 1, 1, 0, -1], 9), ([1, 0, 0, 0, 1, 1, -2], 18), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, -1, 0, 0, 1, -1], 9)]

theorem source443_checked : normalize (row ![0, -1, 0, 1, 1, -1] ![0, -1, 0, 0, 0, 1] (3, 3)) = source443 := by
  decide +kernel

theorem source443_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source443 (momentValues f) = 0 := by
  rw [← source443_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source444 : Sparse := [([0, -2, -1, 1, 0, 1, 1], 9), ([0, -2, -1, 1, 1, 0, 1], -9), ([0, -2, -1, 2, 0, 0, 1], 9), ([0, -2, 0, 1, 0, 0, 1], 9), ([0, -1, -2, 1, 0, 1, 1], -9), ([0, -1, -2, 1, 1, 0, 1], 9), ([0, -1, -2, 2, 0, 0, 1], 9), ([0, -1, -1, 0, 0, 0, 2], 18), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 1, 0, 1, 0], 9), ([0, -1, -1, 1, 1, -1, 1], 9), ([0, -1, -1, 1, 1, 0, 0], 9), ([0, -1, 0, 1, 0, -1, 1], 9), ([0, 0, -2, 1, 0, 0, 1], 9), ([0, 0, -1, 1, -1, 0, 1], 9), ([1, -2, -1, 1, 0, 1, 1], 9), ([1, -2, 0, 1, 0, 0, 1], 9), ([1, -1, -2, 1, 1, 0, 1], 9), ([1, -1, -1, 0, 0, 0, 2], 18), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 1, -1, 1], 9), ([1, -1, -1, 2, -1, 0, 1], 9), ([1, -1, -1, 2, 0, -1, 1], 9), ([1, -1, 0, 1, -1, 0, 1], -9), ([1, -1, 0, 1, 0, -1, 1], 9), ([1, -1, 0, 1, 0, 0, 0], 9), ([1, 0, -2, 1, 0, 0, 1], 9), ([1, 0, -1, 1, -1, 0, 1], 9), ([1, 0, -1, 1, 0, -1, 1], -9), ([1, 0, -1, 1, 0, 0, 0], 9)]

theorem source444_checked : normalize (row ![-1, -1, 1, 0, 0, 1] ![0, 0, 1, 0, 0, -1] (3, 3)) = source444 := by
  decide +kernel

theorem source444_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source444 (momentValues f) = 0 := by
  rw [← source444_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source445 : Sparse := [([0, 0, 1, -1, 0, 0, 0], -9), ([0, 0, 1, -1, 0, 1, -1], 9), ([0, 1, 0, -1, 0, 0, 0], -9), ([0, 1, 0, -1, 1, 0, -1], 9), ([0, 1, 1, -2, 0, 1, -1], -9), ([0, 1, 1, -2, 1, 0, -1], -9), ([0, 1, 1, -1, -1, 0, 0], 9), ([0, 1, 1, -1, 0, -1, 0], 9), ([0, 1, 2, -2, 0, 0, -1], 9), ([0, 1, 2, -1, 0, -1, -1], -9), ([0, 2, 1, -2, 0, 0, -1], 9), ([0, 2, 1, -1, -1, 0, -1], -9), ([1, 0, 1, -1, 0, 0, 0], -9), ([1, 0, 1, -1, 0, 1, -1], 9), ([1, 0, 1, -1, 1, 0, -1], -9), ([1, 0, 2, -1, 0, 0, -1], -9), ([1, 1, 0, -1, 0, 0, 0], -9), ([1, 1, 0, -1, 0, 1, -1], -9), ([1, 1, 0, -1, 1, 0, -1], 9), ([1, 1, 1, -2, 0, 1, -1], -9), ([1, 1, 1, -2, 1, 0, -1], -9), ([1, 1, 1, -1, -1, 1, -1], -9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 1, 1, 0, 0, 0, -2], -18), ([1, 1, 2, -1, -1, 0, -1], -9), ([1, 2, 0, -1, 0, 0, -1], -9), ([1, 2, 1, -1, 0, -1, -1], -9)]

theorem source445_checked : normalize (row ![1, 1, -1, 0, 0, -1] ![0, 0, -1, 0, 0, 1] (0, -3)) = source445 := by
  decide +kernel

theorem source445_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source445 (momentValues f) = 0 := by
  rw [← source445_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source446 : Sparse := [([0, -2, 0, 1, 0, 0, 1], 9), ([0, -2, 0, 2, -1, 0, 1], -9), ([0, -1, -1, 1, -1, 1, 1], 9), ([0, -1, -1, 2, -1, 0, 1], -9), ([0, -1, 0, 1, -1, 1, 0], -9), ([0, -1, 0, 1, 0, 0, 0], -9), ([0, -1, 0, 2, -2, 0, 1], 9), ([0, -1, 0, 2, -1, -1, 1], 9), ([0, -1, 1, 1, -2, 0, 1], -9), ([0, -1, 1, 1, -1, 0, 0], 9), ([0, 0, 0, 1, -1, -1, 1], -9), ([0, 0, 0, 1, -1, 0, 0], 9), ([1, -2, 0, 1, -1, 1, 1], -9), ([1, -2, 0, 1, 0, 0, 1], 9), ([1, -2, 0, 2, -1, 0, 1], -9), ([1, -2, 1, 1, -1, 0, 1], -9), ([1, -1, -1, 1, -1, 1, 1], 9), ([1, -1, -1, 1, 0, 0, 1], -9), ([1, -1, -1, 2, -1, 0, 1], -9), ([1, -1, 0, 0, -1, 0, 2], -18), ([1, -1, 0, 1, -2, 1, 1], -9), ([1, -1, 0, 1, -1, 1, 0], -9), ([1, -1, 0, 1, 0, -1, 1], -9), ([1, -1, 0, 1, 0, 0, 0], -9), ([1, -1, 1, 1, -1, -1, 1], -9), ([1, 0, -1, 1, -1, 0, 1], -9), ([1, 0, 0, 1, -2, 0, 1], -9)]

theorem source446_checked : normalize (row ![-1, 0, 1, -1, 0, 1] ![0, 0, 1, 0, 0, -1] (0, -3)) = source446 := by
  decide +kernel

theorem source446_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source446 (momentValues f) = 0 := by
  rw [← source446_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

def source447 : Sparse := [([0, 0, 0, -1, 1, 0, 0], 9), ([0, 0, 0, -1, 1, 1, -1], -9), ([0, 0, 0, -1, 2, 0, -1], 9), ([0, 0, 1, -1, 1, 0, -1], 9), ([0, 1, -1, -1, 1, 0, 0], 9), ([0, 1, -1, -1, 1, 1, -1], 9), ([0, 1, -1, -1, 2, 0, -1], -9), ([0, 1, 0, -2, 1, 1, -1], 9), ([0, 1, 0, -2, 2, 0, -1], 9), ([0, 1, 0, -1, 0, 1, -1], 9), ([0, 1, 0, -1, 2, -1, -1], 9), ([0, 1, 0, 0, 1, 0, -2], 18), ([0, 1, 1, -1, 0, 0, -1], 9), ([0, 2, -1, -1, 1, 0, -1], 9), ([0, 2, 0, -1, 1, -1, -1], 9), ([1, 0, 0, -1, 2, 0, -1], 9), ([1, 0, 1, -1, 1, 0, -1], 9), ([1, 1, -1, -1, 1, 1, -1], 9), ([1, 1, 0, -1, 0, 0, 0], 9), ([1, 1, 0, -1, 0, 1, -1], 9), ([1, 1, 0, -1, 1, -1, 0], 9), ([1, 1, 0, -1, 2, -1, -1], 9), ([1, 1, 0, 0, 1, 0, -2], 18), ([1, 1, 1, -2, 1, 0, -1], 9), ([1, 1, 1, -1, 0, 0, -1], 9), ([1, 1, 1, -1, 1, -1, -1], -9), ([1, 2, -1, -1, 1, 0, -1], 9), ([1, 2, 0, -2, 1, 0, -1], 9), ([1, 2, 0, -1, 0, 0, -1], -9), ([1, 2, 0, -1, 1, -1, -1], 9)]

theorem source447_checked : normalize (row ![1, 0, -1, 1, 0, -1] ![0, 0, -1, 0, 0, 1] (3, 3)) = source447 := by
  decide +kernel

theorem source447_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source447 (momentValues f) = 0 := by
  rw [← source447_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
